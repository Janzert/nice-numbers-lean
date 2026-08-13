/-
  NiceNumbers.lean
  ================

  Six theorems about nice / quasi-nice numbers, formalised in Lean 4.

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

  **Theorem C** (`residues_nonempty_iff`, `residues_empty_iff`,
  `residues_single_nonempty_iff`): the residue set `R_b = {ρ : ρ^e₁+ρ^e₂ ≡ T}` is
  **empty iff `a = 1`, or `a ≥ 3` with `e₂-e₁` even and `e₁ ∤ a-1`**, where
  `a = v₂(b-1)`.  No odd prime divisor of `b-1` enters: modulo the odd part `T`
  vanishes and `ρ = 0` is a residue, so the whole classification is a valuation
  count at 2.  Theorem B is its `a = 1` case.  For a single exponent `n^e` the
  rule is `R_b ≠ ∅` iff `a = 0` or `e ∣ a-1`.

  **Theorem G** (`no_nice_of_universal_clash`, `clash_iff_dvd_clashMod`,
  `clash_prime_pow_iff`): if `x^e₁ ≡ x^e₂ (mod b)` for *every* `x` — a universal
  last-digit clash — then no `n` is pandigital in base `b`.  The bases where that
  happens are **exactly the divisors of one number** `N(e₁,e₂)`, computed here as
  a finite gcd (`N(1,3) = 6`, `N(2,4) = 12`, `N(3,7) = 120`, `N(2,3) = 2`); and
  `p^a ∣ N` iff `a ≤ e₁` and every unit mod `p` has order dividing `e₂-e₁`, which
  is `λ(p^a) ∣ e₂-e₁` once the unit group's exponent is known.  Evaluating that
  exponent is the one step of Theorem G left unformalised.

  **Theorem F** (`greedy_distinct_slots`, `theorem_F`): the one *constructive*
  result here rather than an impossibility.  With `gcd(e₁e₂, b) = 1`, a starting
  digit `ρ` and a unit `β` separating the two progressions, if `4(d-1) + 2 < b`
  then some `d`-digit `n` has `2d` pairwise-distinct low slots, hence combined
  digit deficiency at most `b - 2d`.  Since `d ≈ b/E` that is `b(1 - 2/E)`: the
  same `2/E` as the DFS prune, reached from the constructive side.

  Together these replace exhaustive machine checks over `e₁ ≤ 8`, `e₂ ≤ 9`,
  `b < 400` (A, B, C), `b < 500`, five pairs, ~2700 values of `n` (D), and
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

/-! ## §6  Proposition C′ — how complete the congruence sieve is

A *congruence sieve* at modulus `m` prunes a candidate `n` by testing
`(n^e₁ + n^e₂) mod m` for membership in the set of residues that a pandigital
pair can have.  Proposition C′ of the report claims that set is always exactly
the one the digit-sum congruence already gives — that **no** modulus adds
information.  This section formalises the two halves of that claim, and they
come out differently:

* **Soundness** (`sieve_sound_mod_pred`, `valOf_mod_pow_sub_one`) — the half that
  is true for every modulus.  Casting out `b-1`s pins `x + y` mod `b-1`, and
  more generally `x + y ≡ Σ_t b^t S_t (mod b^j - 1)` where `S_t` totals the
  digits in positions `≡ t (mod j)`.  This is the engine of the whole
  proposition: it is why only `j = ord_m(b)` matters, and why the block sizes
  `c_t` are the only combinatorial data.
* **Completeness** — the claim that nothing beyond that survives.  It is
  **false**, and `base_four_sieve_is_incomplete` is a machine-checked
  counterexample: in base 4 with digit lengths `(2,2)` — a genuine `(2,3)` band,
  `n = 2` lies in it — the digit-sum congruence permits all five residues mod 5,
  and only three occur.  So a modulus *can* buy density the digit sum does not.

See REPORT-provability.md §6 for what is true instead: completeness holds under
an explicit hypothesis on the block sizes, the deficiency elsewhere is tiny
(base 10 loses 2 residues in 11111), and the sharp threshold is conjectural. -/

/-! ### §6.0  Little-endian values, and folding the weights mod `b^j - 1` -/

/-- Value of a digit list, least significant digit first. -/
def valOf (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + b * valOf b ds

/-- `Σ_i b^(i mod j) · dᵢ` — the same sum with the weights folded to period `j`.
The accumulator `t` is the current position mod `j`. -/
def wsum (b j : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | t, d :: ds => b ^ t * d + wsum b j ((t + 1) % j) ds

theorem wsum_nil (b j t : Nat) : wsum b j t [] = 0 := rfl

theorem wsum_cons (b j t d : Nat) (ds : List Nat) :
    wsum b j t (d :: ds) = b ^ t * d + wsum b j ((t + 1) % j) ds := rfl

/-- `x^q ≡ 1 (mod x-1)`, the reason weights are periodic at all. -/
theorem pow_mod_pred {x : Nat} (hx : 1 ≤ x) : ∀ q, x ^ q % (x - 1) = 1 % (x - 1) := by
  intro q
  induction q with
  | zero => rw [Nat.pow_zero]
  | succ k ih =>
    have hstep : x % (x - 1) = 1 % (x - 1) := by
      have h := Nat.add_mod_left (x - 1) 1
      rwa [show x - 1 + 1 = x from by omega] at h
    rw [Nat.pow_succ, Nat.mul_mod, ih, hstep, ← Nat.mul_mod, Nat.one_mul]

/-- Weights are periodic mod `b^j - 1`: only `u mod j` matters. -/
theorem pow_mod_cycle {b j : Nat} (hb : 1 < b) (hj : 0 < j) (u : Nat) :
    b ^ u % (b ^ j - 1) = b ^ (u % j) % (b ^ j - 1) := by
  have hbj : 1 ≤ b ^ j := Nat.pow_pos (by omega)
  have key : b ^ u = (b ^ j) ^ (u / j) * b ^ (u % j) := by
    rw [← Nat.pow_mul, ← Nat.pow_add, Nat.div_add_mod]
  rw [key, Nat.mul_mod, pow_mod_pred hbj (u / j), ← Nat.mul_mod, Nat.one_mul]

/--
**The block congruence.**  `b^t · valOf b ds ≡ wsum b j t ds (mod b^j - 1)`:
reducing mod `b^j - 1` collapses the digit positions into `j` residue classes,
and only the total of each class survives.  Everything §6 says about which
moduli can see what comes from this one identity.
-/
theorem valOf_mod_wsum {b j : Nat} (hb : 1 < b) (hj : 0 < j) :
    ∀ (ds : List Nat) (t : Nat),
      (b ^ t * valOf b ds) % (b ^ j - 1) = wsum b j (t % j) ds % (b ^ j - 1) := by
  intro ds
  induction ds with
  | nil => intro t; show (b ^ t * 0) % _ = 0 % _; rw [Nat.mul_zero]
  | cons d ds ih =>
    intro t
    have hsplit : b ^ t * valOf b (d :: ds) = b ^ t * d + b ^ (t + 1) * valOf b ds := by
      show b ^ t * (d + b * valOf b ds) = _
      rw [Nat.mul_add, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm b (valOf b ds)]
    have hidx : (t % j + 1) % j = (t + 1) % j := Nat.mod_add_mod t j 1
    rw [hsplit, wsum_cons, hidx, Nat.add_mod, Nat.add_mod (b ^ (t % j) * d),
        Nat.mul_mod (b ^ t) d, Nat.mul_mod (b ^ (t % j)) d,
        pow_mod_cycle hb hj t, ih (t + 1)]

/-- The block congruence at `t = 0`, which is the form actually used. -/
theorem valOf_mod_pow_sub_one {b j : Nat} (hb : 1 < b) (hj : 0 < j) (ds : List Nat) :
    valOf b ds % (b ^ j - 1) = wsum b j 0 ds % (b ^ j - 1) := by
  have h := valOf_mod_wsum hb hj ds 0
  rwa [Nat.pow_zero, Nat.one_mul, Nat.zero_mod] at h

/--
**Only the block totals are visible.**  For any modulus dividing `b^j - 1`, the
pair `(x,y)` enters the sieve only through `wsum b j 0` of each digit list — the
`j` totals of the digits in positions `≡ t (mod j)`.  This is why the block
sizes are the sole combinatorial data in §6, and why `j = ord_m(b)` is the only
feature of `m` that matters.
-/
theorem pair_mod_pow_sub_one {b j : Nat} (hb : 1 < b) (hj : 0 < j) (d₁ d₂ : List Nat) :
    (valOf b d₁ + valOf b d₂) % (b ^ j - 1)
      = (wsum b j 0 d₁ + wsum b j 0 d₂) % (b ^ j - 1) := by
  rw [Nat.add_mod, valOf_mod_pow_sub_one hb hj, valOf_mod_pow_sub_one hb hj, ← Nat.add_mod]

/-- At `j = 1` the weights collapse to `1` and `wsum` is the plain digit sum. -/
theorem wsum_one (b : Nat) : ∀ ds : List Nat, wsum b 1 0 ds = ds.sum := by
  intro ds
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [wsum_cons, ih]; simp

/-- **Casting out `b-1`s, for lists.**  The `j = 1` case of the block
congruence, and the only congruence Proposition C′ claims is available. -/
theorem valOf_mod_pred {b : Nat} (hb : 1 < b) (ds : List Nat) :
    valOf b ds % (b - 1) = ds.sum % (b - 1) := by
  have h := valOf_mod_pow_sub_one hb Nat.one_pos ds
  rwa [Nat.pow_one, wsum_one] at h

/-- **Soundness of the digit-sum sieve.**  A pandigital pair has
`x + y ≡ T (mod b-1)`, where `T` is the total of all `b` digits.  Stated on the
digit lists, so it holds for any notion of solution whose digits are those
lists — the same convention §1-§3 use. -/
theorem sieve_sound_mod_pred {b T : Nat} (hb : 1 < b) (d₁ d₂ : List Nat)
    (hT : d₁.sum + d₂.sum = T) :
    (valOf b d₁ + valOf b d₂) % (b - 1) = T % (b - 1) := by
  rw [Nat.add_mod, valOf_mod_pred hb, valOf_mod_pred hb, ← Nat.add_mod, hT]

/-- `valOf` inverts `digits`, so everything above is about actual numbers and
not merely about lists that resemble digits. -/
theorem valOf_digits {b : Nat} (hb : 1 < b) : ∀ x, valOf b (digits b x) = x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [digits_zero]; rfl
    · rw [digits_step hb hx]
      show x % b + b * valOf b (digits b (x / b)) = x
      rw [ih (x / b) (Nat.div_lt_self hx hb)]
      exact Nat.mod_add_div x b

/-- …and `digitSum` of §0 is the sum of that list, so §6 and §2 are talking
about the same quantity. -/
theorem digitSum_eq_sum {b : Nat} (hb : 1 < b) : ∀ x, digitSum b x = (digits b x).sum := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [digitSum_zero, digits_zero]; rfl
    · rw [digitSum_step hb hx, digits_step hb hx, ih (x / b) (Nat.div_lt_self hx hb)]
      simp

/-- **Soundness, on numbers.**  Whatever else a sieve knows, it never learns
more than this about `x + y` from a modulus dividing `b-1`. -/
theorem sieve_sound {b x y T : Nat} (hb : 1 < b)
    (hT : digitSum b x + digitSum b y = T) :
    (x + y) % (b - 1) = T % (b - 1) := by
  have h := sieve_sound_mod_pred (b := b) (T := T) hb (digits b x) (digits b y)
    (by rw [← digitSum_eq_sum hb, ← digitSum_eq_sum hb]; exact hT)
  rwa [valOf_digits hb, valOf_digits hb] at h

/-! ### §6.1  Completeness fails — a machine-checked counterexample

Base 4 with digit lengths `(2,2)`.  That is a genuine `(2,3)` band: `n = 2` has
`2² = 4 = "10"` and `2³ = 8 = "20"`, two base-4 digits each, and `2 + 2 = 4 = b`,
so Theorem A's length identity holds and neither A (`4 % 5 ≠ 1`) nor B
(`4 % 4 ≠ 3`) kills the base.

`gcd(5, b-1) = gcd(5,3) = 1`, so the digit-sum congruence mod 3 excludes **no**
residue mod 5 whatsoever — Proposition C′ therefore predicts all five occur.
Only three do.  The three attainable sums are `15, 18, 21`; all are `≡ 0 (mod 3)`
as casting out 3s demands, and mod 5 they are `0, 3, 1`. -/

/-- A number with exactly two base-`b` digits has the digit list you expect.
Same two-`digits_step` unfolding as `digits_69sq`, done once and generically. -/
theorem digits_two {b x : Nat} (hb : 1 < b) (h1 : b ≤ x) (h2 : x < b * b) :
    digits b x = [x % b, x / b] := by
  have hx : 0 < x := by omega
  have hq : 0 < x / b := Nat.div_pos h1 (by omega)
  have hqb : x / b < b := Nat.div_lt_of_lt_mul h2
  have hq2 : x / b / b = 0 := Nat.div_eq_of_lt hqb
  rw [digits_step hb hx, digits_step hb hq, hq2, digits_zero, Nat.mod_eq_of_lt hqb]

/-- The finite heart of the counterexample, and it pins the image exactly: over
every pair of two-digit base-4 numbers, a pandigital one sums to `0`, `1` or `3`
mod 5 — never `2`, never `4`.  256 cases, checked by the kernel.  (The
hypotheses are conjoined rather than curried purely so that
`Nat.decidableBallLT` instance search succeeds; curried, it gives up.) -/
theorem base_four_gap_core :
    ∀ x < 16, ∀ y < 16,
      (4 ≤ x ∧ 4 ≤ y ∧ ∀ v < 4, occ v [x % 4, x / 4, y % 4, y / 4] = 1) →
      ((x + y) % 5 = 0 ∨ (x + y) % 5 = 1 ∨ (x + y) % 5 = 3) := by decide

/-- Lifting the finite check off the digit lists and onto the numbers. -/
theorem base_four_image {x y : Nat}
    (hx : numDigits 4 x = 2) (hy : numDigits 4 y = 2)
    (hpan : ∀ v, v < 4 → occ v (digits 4 x ++ digits 4 y) = 1) :
    (x + y) % 5 = 0 ∨ (x + y) % 5 = 1 ∨ (x + y) % 5 = 3 := by
  obtain ⟨hx1, hx2⟩ := bounds_of_numDigits (b := 4) (by decide) x 1 hx
  obtain ⟨hy1, hy2⟩ := bounds_of_numDigits (b := 4) (by decide) y 1 hy
  rw [Nat.pow_one] at hx1 hy1
  rw [show (4 : Nat) ^ (1 + 1) = 16 from by decide] at hx2 hy2
  have hdx : digits 4 x = [x % 4, x / 4] := digits_two (by decide) hx1 (by omega)
  have hdy : digits 4 y = [y % 4, y / 4] := digits_two (by decide) hy1 (by omega)
  rw [hdx, hdy] at hpan
  exact base_four_gap_core x hx2 y hy2 ⟨hx1, hy1, fun v hv => hpan v hv⟩

/--
**Proposition C′ is false.**  In base 4 with digit lengths `(2,2)`, no pandigital
pair has `x + y ≡ 2 (mod 5)` — while the digit-sum congruence, the only thing
Proposition C′ allows a sieve to know, permits every residue mod 5 because
`gcd(5, 4-1) = 1`.  So the modulus 5 is strictly stronger than casting out 3s,
and "no modulus yields additional density" does not hold as stated.
-/
theorem base_four_sieve_is_incomplete {x y : Nat}
    (hx : numDigits 4 x = 2) (hy : numDigits 4 y = 2)
    (hpan : ∀ v, v < 4 → occ v (digits 4 x ++ digits 4 y) = 1) :
    (x + y) % 5 ≠ 2 := by
  rcases base_four_image hx hy hpan with h | h | h <;> omega

/-- The same for `4`: two of the five residues are unreachable, so the sieve
mod 5 keeps `3/5` of the residues where casting out 3s keeps all of them. -/
theorem base_four_sieve_is_incomplete' {x y : Nat}
    (hx : numDigits 4 x = 2) (hy : numDigits 4 y = 2)
    (hpan : ∀ v, v < 4 → occ v (digits 4 x ++ digits 4 y) = 1) :
    (x + y) % 5 ≠ 4 := by
  rcases base_four_image hx hy hpan with h | h | h <;> omega

/-- Non-vacuity *and* sharpness, which an impossibility statement about an empty
hypothesis set would have neither of.  The three pandigital base-4 pairs are
`(4,11)`, `(4,14)` and `(9,12)`, with sums `15, 18, 21` — every one `≡ 0 (mod 3)`
as casting out 3s demands, and mod 5 they are exactly `0, 3, 1`.  So `{0,1,3}` in
`base_four_gap_core` is attained, not merely permitted. -/
theorem base_four_attained :
    ((∀ v, v < 4 → occ v (digits 4 4 ++ digits 4 11) = 1) ∧ (4 + 11) % 5 = 0) ∧
    ((∀ v, v < 4 → occ v (digits 4 4 ++ digits 4 14) = 1) ∧ (4 + 14) % 5 = 3) ∧
    ((∀ v, v < 4 → occ v (digits 4 9 ++ digits 4 12) = 1) ∧ (9 + 12) % 5 = 1) := by
  have h4 : digits 4 4 = [0, 1] := digits_two (by decide) (by decide) (by decide)
  have h9 : digits 4 9 = [1, 2] := digits_two (by decide) (by decide) (by decide)
  have h11 : digits 4 11 = [3, 2] := digits_two (by decide) (by decide) (by decide)
  have h12 : digits 4 12 = [0, 3] := digits_two (by decide) (by decide) (by decide)
  have h14 : digits 4 14 = [2, 3] := digits_two (by decide) (by decide) (by decide)
  refine ⟨⟨?_, by decide⟩, ⟨?_, by decide⟩, ⟨?_, by decide⟩⟩
  · rw [h4, h11]; decide
  · rw [h4, h14]; decide
  · rw [h9, h12]; decide

/-- And the lengths are right, so this really is the `(2,2)` split: `4`, `9`,
`11`, `12` and `14` all have exactly two base-4 digits. -/
theorem base_four_lengths :
    numDigits 4 4 = 2 ∧ numDigits 4 9 = 2 ∧ numDigits 4 11 = 2 ∧
    numDigits 4 12 = 2 ∧ numDigits 4 14 = 2 :=
  ⟨numDigits_eq_of_bounds (by decide) (by decide) (by decide),
   numDigits_eq_of_bounds (by decide) (by decide) (by decide),
   numDigits_eq_of_bounds (by decide) (by decide) (by decide),
   numDigits_eq_of_bounds (by decide) (by decide) (by decide),
   numDigits_eq_of_bounds (by decide) (by decide) (by decide)⟩

/-- Base 4 is a genuine `(2,3)` band and not an artefact: `n = 2` has
`2² = "10"` and `2³ = "20"`, two base-4 digits each, so the length identity
`2 + 2 = 4 = b` holds.  Neither Theorem A (`4 % 5 ≠ 1`) nor Theorem B
(`4 % 4 ≠ 3`) kills the base, so the counterexample sits inside the family this
repo actually searches. -/
theorem base_four_band_nonempty : InBand 4 2 3 2 := by
  show numDigits 4 (2 ^ 2) + numDigits 4 (2 ^ 3) = 4
  rw [numDigits_eq_of_bounds (b := 4) (x := 2 ^ 2) (k := 1) (by decide) (by decide) (by decide),
      numDigits_eq_of_bounds (b := 4) (x := 2 ^ 3) (k := 1) (by decide) (by decide) (by decide)]

/-! ## §7  Theorem C — the complete classification of `R_b = ∅`

The residue set `R_b = {ρ : ρ^e₁ + ρ^e₂ ≡ T (mod b-1)}`, `2T = b(b-1)`, is the
second necessary condition every solution satisfies (§2 refuted it for
`b ≡ 3 mod 4`).  This section decides emptiness **for every base and every pair**,
and the answer is entirely 2-adic: writing `b - 1 = 2^a · m` with `m` odd,

> `R_b = ∅`  ⟺  `a = 1`, or (`a ≥ 3` and `e₂ - e₁` even and `e₁ ∤ a - 1`).

The reason no odd prime enters is `ρ = 0`.  Modulo the odd part of `b-1` the
target `T` vanishes — `2T = b(b-1)` and `b-1`'s odd part divides `T` — so the odd
part imposes no condition at all, and the CRT decomposition the informal proof
reaches for is never needed.  What is left is the 2-part, where `T ≡ 2^(a-1)`,
and the whole question becomes: which 2-adic valuations can `ρ^e₁ + ρ^e₂` have?
Exactly `1` (from odd `ρ` with `e₂-e₁` even), whatever `v₂(1 + ρ^(e₂-e₁))` is
(odd `ρ`, `e₂-e₁` odd — always `≥ 1`), and the multiples of `e₁` (from even `ρ`).
Never `0`, which is Theorem B.

Theorem B is therefore the `a = 1` case of this theorem, and the three "extra"
2-adic dead classes the report found for `(2,4)`, `(4,6)` and `(3,7)` are the
second clause.  §7.5 runs both ends on numerals.
-/

/-! ### §7.0  A two-adic toolkit -/

theorem pow_two_eq (x : Nat) : x ^ 2 = x * x := by rw [Nat.pow_succ, Nat.pow_one]

theorem mul_pow_two_comm (p q m : Nat) : (2^p * m) * (2^q * m) = 2^(p+q) * (m*m) := by
  rw [Nat.pow_add, Nat.mul_assoc, ← Nat.mul_assoc m (2^q) m, Nat.mul_comm m (2^q),
      Nat.mul_assoc, ← Nat.mul_assoc]

theorem odd_pow {u : Nat} (hu : u % 2 = 1) (e : Nat) : u ^ e % 2 = 1 := by
  induction e with
  | zero => simp
  | succ j ih => rw [Nat.pow_succ, Nat.mul_mod, ih, hu]

/-- an odd square is `1` mod 4 -- the only fact about squares this section needs. -/
theorem odd_sq_mod_four {x : Nat} (hx : x % 2 = 1) : x ^ 2 % 4 = 1 % 4 := by
  obtain ⟨t, ht⟩ : ∃ t, x = 2 * t + 1 := ⟨x / 2, by omega⟩
  have hsq : x ^ 2 = 4 * (t * t) + 4 * t + 1 := by
    rw [pow_two_eq, ht, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul,
        Nat.mul_assoc, Nat.mul_left_comm t 2 t, ← Nat.mul_assoc]
    omega
  omega

/-- `(b-1)/2 = 2^(a-1)·m` is `2^(a-1)` mod `2^a`: the target, localised. -/
theorem half_mod {a m : Nat} (hm : m % 2 = 1) : (2 ^ a * m) % (2 ^ (a+1)) = 2 ^ a := by
  obtain ⟨t, ht⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
  have h : 2 ^ a * m = 2 ^ a + 2 ^ (a+1) * t := by
    rw [ht, Nat.mul_add, Nat.mul_one, Nat.pow_succ, Nat.mul_comm (2^a) 2, ← Nat.mul_assoc,
        Nat.mul_comm (2^a) 2, Nat.mul_assoc, Nat.add_comm]
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- every positive natural is `2^v` times an odd number -/
theorem two_adic_split : ∀ x : Nat, 0 < x → ∃ v u, x = 2 ^ v * u ∧ u % 2 = 1 := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx
    by_cases h : x % 2 = 1
    · exact ⟨0, x, by simp, h⟩
    · obtain ⟨y, hy⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
      obtain ⟨v, u, hu, hodd⟩ := ih y (by omega) (by omega)
      refine ⟨v + 1, u, ?_, hodd⟩
      rw [hy, hu, Nat.pow_succ, Nat.mul_comm (2^v) 2, Nat.mul_assoc]

/-- ...and the exponent is determined, which is the whole of "the 2-adic
valuation is well defined".  Used only through the equality `2^i·U = 2^j·V`. -/
theorem two_pow_odd_unique {i j U V : Nat} (hU : U % 2 = 1) (hV : V % 2 = 1)
    (h : 2 ^ i * U = 2 ^ j * V) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · obtain ⟨s, hs⟩ : ∃ s, j = i + (s + 1) := ⟨j - i - 1, by omega⟩
    rw [hs, Nat.pow_add, Nat.mul_assoc] at h
    have := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide) (n := i)) h
    have h2 : (2 ^ (s+1) * V) % 2 = 0 := by
      rw [Nat.pow_succ, Nat.mul_comm (2^s) 2, Nat.mul_assoc, Nat.mul_mod_right]
    omega
  · exact heq
  · obtain ⟨s, hs⟩ : ∃ s, i = j + (s + 1) := ⟨i - j - 1, by omega⟩
    rw [hs, Nat.pow_add, Nat.mul_assoc] at h
    have := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide) (n := j)) h
    have h2 : (2 ^ (s+1) * U) % 2 = 0 := by
      rw [Nat.pow_succ, Nat.mul_comm (2^s) 2, Nat.mul_assoc, Nat.mul_mod_right]
    omega

theorem pow_mod_one {x M : Nat} (h : x % M = 1 % M) (c : Nat) : x ^ c % M = 1 % M := by
  induction c with
  | zero => simp
  | succ j ih => rw [Nat.pow_succ, Nat.mul_mod, ih, h, ← Nat.mul_mod, Nat.one_mul]

/-- a square root of `1` is fixed by odd powers and trivialised by even ones -/
theorem pow_mod_sq_one {x M : Nat} (h : x ^ 2 % M = 1 % M) :
    ∀ k, x ^ (2 * k) % M = 1 % M ∧ x ^ (2 * k + 1) % M = x % M := by
  have h' : x * x % M = 1 % M := by rw [← pow_two_eq]; exact h
  intro k
  induction k with
  | zero => simp
  | succ j ih =>
    have heven : x ^ (2 * (j+1)) % M = 1 % M := by
      have hstep : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [hstep, Nat.pow_succ, Nat.mul_mod, ih.2, ← Nat.mul_mod, h']
    exact ⟨heven, by rw [Nat.pow_succ, Nat.mul_mod, heven, ← Nat.mul_mod, Nat.one_mul]⟩

/-! ### §7.1  The target `T`, reduced

`T = b(b-1)/2` mod `b-1` is `(b-1)/2` when `b` is odd and `0` when `b` is even.
Both are one line and neither needs `b` again afterwards. -/

theorem target_eq {b T A : Nat} (hb : 1 < b) (hT : 2 * T = b * (b - 1))
    (hA : 2 * A = b - 1) : T % (b - 1) = A % (b - 1) := by
  have hb1 : b = (b - 1) + 1 := by omega
  have h2 : 2 * T = ((b-1) + 1) * (b - 1) := by rw [← hb1]; exact hT
  rw [← hA] at h2
  have hAA : A * (2 * A) = 2 * (A * A) := by rw [Nat.mul_left_comm]
  have hexp : (2 * A + 1) * (2 * A) = 4 * (A * A) + 2 * A := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, hAA]; omega
  rw [hexp] at h2
  have hTv : T = A + (b - 1) * A := by
    have hswap : (b - 1) * A = 2 * (A * A) := by rw [← hA, Nat.mul_assoc]
    omega
  rw [hTv, Nat.add_mul_mod_self_left]

theorem target_zero {b T : Nat} (hb : 1 < b) (hT : 2 * T = b * (b - 1))
    (hbe : b % 2 = 0) : T % (b - 1) = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, b = 2 * c := ⟨b / 2, by omega⟩
  have hstep : b * (b - 1) = 2 * (c * (b - 1)) := by rw [hc, Nat.mul_assoc]
  have hTv : T = c * (b - 1) := by omega
  rw [hTv, Nat.mul_mod_left]

/-! ### §7.2  The live direction: four explicit residues

Each live class gets a residue written down, so this half of the theorem needs
no existence argument and, in particular, no Chinese remainder theorem. -/

/-- The shape two of the four witnesses reduce to: if the sum is `2^w · m · W`
with `W` odd and `b - 1 = 2^(w+1)·m`, it is congruent to `T`. -/
theorem residue_of_odd_cofactor {b T w m W S : Nat} (hb : 1 < b) (hT : 2 * T = b * (b - 1))
    (hM : b - 1 = 2 ^ (w+1) * m) (hW : W % 2 = 1) (hS : S = 2 ^ w * (m * W)) :
    S % (b - 1) = T % (b - 1) := by
  have h2A : 2 * (2 ^ w * m) = b - 1 := by rw [hM, ← Nat.mul_assoc, ← Nat.pow_succ']
  obtain ⟨W', hW'⟩ : ∃ W', W = 2 * W' + 1 := ⟨W / 2, by omega⟩
  have hval : S = 2 ^ w * m + (b - 1) * W' := by
    rw [hS, hW', hM, Nat.pow_succ, Nat.mul_add m (2 * W') 1, Nat.mul_one,
        Nat.mul_add (2 ^ w) (m * (2 * W')) m, Nat.mul_left_comm m 2 W',
        ← Nat.mul_assoc (2 ^ w) 2 (m * W'), ← Nat.mul_assoc (2 ^ w * 2) m W']
    omega
  rw [hval, Nat.add_mul_mod_self_left, target_eq hb hT h2A]

/-- `a = 0`, i.e. `b` even: `ρ = 0`, because then `T ≡ 0 (mod b-1)`. -/
theorem residue_of_even_base {b e₁ e₂ T : Nat} (hb : 1 < b) (he₁ : 1 ≤ e₁) (he₂ : 1 ≤ e₂)
    (hT : 2 * T = b * (b - 1)) (hbe : b % 2 = 0) :
    (0 ^ e₁ + 0 ^ e₂) % (b - 1) = T % (b - 1) := by
  rw [Nat.zero_pow (by omega), Nat.zero_pow (by omega), target_zero hb hT hbe]
  simp

/-- `x + 1 = A`, `2A = M` and `M ∣ A²` make `x` a square root of `1` mod `M`.
With `A = M/2` the cross term `2x = M - 2` is the point: it wipes out `-2A`. -/
theorem sq_one_of_half {x A M K : Nat} (hx1 : x + 1 = A) (h2A : 2 * A = M)
    (hAA : A * A = M * K) (hK : 0 < K) : x ^ 2 % M = 1 % M := by
  have hexp : (x + 1) * (x + 1) = x * x + 2 * x + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.one_mul]
    omega
  have hsq : x * x + 2 * x + 1 = A * A := by rw [← hexp, hx1]
  obtain ⟨K', hK'⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hMK : M * K = M * K' + M := by rw [hK', Nat.mul_add, Nat.mul_one]
  have hxx : x * x = 1 + M * K' := by omega
  rw [pow_two_eq, hxx, Nat.add_mul_mod_self_left]

/-- a square root of `1` raised to exponents of opposite parity contributes
`x + 1` — one power gives `x`, the other `1`. -/
theorem pair_pow_sq_one {x M e₁ e₂ : Nat} (h : x ^ 2 % M = 1 % M) (hpar : e₁ % 2 ≠ e₂ % 2) :
    (x ^ e₁ + x ^ e₂) % M = (x + 1) % M := by
  have hpow := pow_mod_sq_one h
  have hfin : ∀ f g : Nat, f % 2 = 0 → g % 2 = 1 →
      (x ^ f % M + x ^ g % M) % M = (x + 1) % M := by
    intro f g hf hg
    obtain ⟨k, hk⟩ : ∃ k, f = 2 * k := ⟨f / 2, by omega⟩
    obtain ⟨l, hl⟩ : ∃ l, g = 2 * l + 1 := ⟨g / 2, by omega⟩
    rw [hk, hl, (hpow k).1, (hpow l).2, ← Nat.add_mod, Nat.add_comm]
  rw [Nat.add_mod]
  rcases Nat.lt_or_ge (e₁ % 2) (e₂ % 2) with h' | h'
  · exact hfin e₁ e₂ (by omega) (by omega)
  · rw [Nat.add_comm (x ^ e₁ % M)]
    exact hfin e₂ e₁ (by omega) (by omega)

/-- `a ≥ 2` and `e₂ - e₁` odd: `ρ = (b-1)/2 - 1`, whose square is `1`, so the two
powers contribute `ρ` and `1` and their sum is `(b-1)/2 ≡ T`.  Note the witness
is *not* `≡ 0` mod the odd part of `b-1`: there it is `-1`, and the two opposite
parities cancel it. -/
theorem residue_of_odd_gap {b e₁ e₂ T c m : Nat} (hb : 1 < b) (hm : m % 2 = 1)
    (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ (c + 2) * m) (hpar : e₁ % 2 ≠ e₂ % 2) :
    ((2 ^ (c+1) * m - 1) ^ e₁ + (2 ^ (c+1) * m - 1) ^ e₂) % (b - 1) = T % (b - 1) := by
  have hmpos : 0 < m := by omega
  have hApos : 0 < 2 ^ (c+1) * m := Nat.mul_pos (Nat.pow_pos (by decide)) hmpos
  have h2A : 2 * (2 ^ (c+1) * m) = b - 1 := by
    rw [hM, ← Nat.mul_assoc, ← Nat.pow_succ']
  have hAA : (2 ^ (c+1) * m) * (2 ^ (c+1) * m) = (b - 1) * (2 ^ c * m) := by
    rw [hM, mul_pow_two_comm, mul_pow_two_comm]
    have hidx : c + 1 + (c + 1) = c + 2 + c := by omega
    rw [hidx]
  have hK : 0 < 2 ^ c * m := Nat.mul_pos (Nat.pow_pos (by decide)) hmpos
  have hsq := sq_one_of_half (x := 2 ^ (c+1) * m - 1) (A := 2 ^ (c+1) * m) (M := b - 1)
    (K := 2 ^ c * m) (by omega) h2A hAA hK
  rw [pair_pow_sq_one hsq hpar]
  have hx1 : (2 ^ (c+1) * m - 1) + 1 = 2 ^ (c+1) * m := by omega
  rw [hx1, target_eq hb hT h2A]

/-- `a = 2`: `ρ = m²`, where `b - 1 = 4m`.  An odd square is `1` mod 8, so the
sum is `m` times something `≡ 2 (mod 4)` — valuation exactly `1 = a - 1`. -/
theorem residue_of_two_adic_two {b e₁ e₂ T m : Nat} (hb : 1 < b) (he₁ : 1 ≤ e₁) (he₂ : 1 ≤ e₂)
    (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ 2 * m) :
    ((m ^ 2) ^ e₁ + (m ^ 2) ^ e₂) % (b - 1) = T % (b - 1) := by
  obtain ⟨f, rfl⟩ : ∃ f, e₁ = f + 1 := ⟨e₁ - 1, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g, e₂ = g + 1 := ⟨e₂ - 1, by omega⟩
  have hpow : ∀ e : Nat, (m ^ 2) ^ (e+1) = m ^ (2 * e + 1) * m := by
    intro e
    rw [← Nat.pow_mul]
    have hidx : 2 * (e + 1) = (2 * e + 1) + 1 := by omega
    rw [hidx, Nat.pow_succ]
  have hZ : (m ^ (2*f+1) + m ^ (2*g+1)) % 4 = 2 := by
    have h1 := (pow_mod_sq_one (M := 4) (odd_sq_mod_four hm) f).2
    have h2 := (pow_mod_sq_one (M := 4) (odd_sq_mod_four hm) g).2
    rw [Nat.add_mod, h1, h2, ← Nat.add_mod]
    omega
  obtain ⟨s, hs⟩ : ∃ s, m ^ (2*f+1) + m ^ (2*g+1) = 2 * (2 * s + 1) :=
    ⟨(m ^ (2*f+1) + m ^ (2*g+1) - 2) / 4, by omega⟩
  refine residue_of_odd_cofactor (w := 1) (m := m) (W := 2 * s + 1) hb hT (by rw [hM])
    (by omega) ?_
  rw [hpow f, hpow g, ← Nat.add_mul, hs, Nat.pow_one, Nat.mul_comm m (2 * s + 1),
      ← Nat.mul_assoc]

/-- `a - 1 = e₁·V` with `V ≥ 1`: `ρ = 2^V·m`, where `b - 1 = 2^a·m`.  Here
`v₂(ρ^e₁ + ρ^e₂) = V·e₁` exactly, because `1 + ρ^(e₂-e₁)` is odd. -/
theorem residue_of_dvd {b e₁ e₂ T m V : Nat} (hb : 1 < b) (he₁ : 1 ≤ e₁) (hlt : e₁ < e₂)
    (hV : 1 ≤ V) (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1))
    (hM : b - 1 = 2 ^ (V * e₁ + 1) * m) :
    ((2 ^ V * m) ^ e₁ + (2 ^ V * m) ^ e₂) % (b - 1) = T % (b - 1) := by
  obtain ⟨V, rfl⟩ : ∃ V', V = V' + 1 := ⟨V - 1, by omega⟩
  obtain ⟨f, hf⟩ : ∃ f, e₁ = f + 1 := ⟨e₁ - 1, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, e₂ = e₁ + (d + 1) := ⟨e₂ - e₁ - 1, by omega⟩
  have hlow : (2 ^ (V+1) * m) ^ e₁ = 2 ^ ((V+1) * e₁) * (m * m ^ f) := by
    rw [Nat.mul_pow, ← Nat.pow_mul, hf, Nat.pow_succ (m := f), Nat.mul_comm (m ^ f) m]
  have hhigh : (2 ^ (V+1) * m) ^ e₂
      = 2 ^ ((V+1) * e₁) * (m * (2 ^ ((V+1) * (d+1)) * (m ^ f * m ^ (d+1)))) := by
    rw [Nat.mul_pow, ← Nat.pow_mul, hd, Nat.mul_add (V+1) e₁ (d+1),
        Nat.pow_add 2 ((V+1) * e₁) ((V+1) * (d+1)),
        Nat.pow_add m e₁ (d+1), hf, Nat.pow_succ (m := f), Nat.mul_comm (m ^ f) m,
        Nat.mul_assoc m (m ^ f) (m ^ (d+1)),
        Nat.mul_assoc (2 ^ ((V+1) * (f+1))) (2 ^ ((V+1) * (d+1))) (m * (m ^ f * m ^ (d+1))),
        Nat.mul_left_comm (2 ^ ((V+1) * (d+1))) m (m ^ f * m ^ (d+1))]
  refine residue_of_odd_cofactor (w := (V+1) * e₁) (m := m)
    (W := m ^ f + 2 ^ ((V+1) * (d+1)) * (m ^ f * m ^ (d+1))) hb hT ?_ ?_ ?_
  · rw [hM, Nat.mul_comm (V+1) e₁]
  · have h1 : m ^ f % 2 = 1 := odd_pow hm f
    have h2 : (2 ^ ((V+1) * (d+1)) * (m ^ f * m ^ (d+1))) % 2 = 0 := by
      obtain ⟨p, hp⟩ : ∃ p, (V+1) * (d+1) = p + 1 :=
        ⟨(V+1)*(d+1) - 1, by
          have := Nat.mul_pos (n := V+1) (m := d+1) (by omega) (by omega); omega⟩
      rw [hp, Nat.pow_succ, Nat.mul_comm (2^p) 2, Nat.mul_assoc, Nat.mul_mod_right]
    omega
  · rw [hlow, hhigh, ← Nat.mul_add (2 ^ ((V+1) * e₁)),
        ← Nat.mul_add m (m ^ f) (2 ^ ((V+1) * (d+1)) * (m ^ f * m ^ (d+1)))]

/-! ### §7.3  The dead direction -/

theorem sum_factor (ρ e₁ d : Nat) : ρ ^ e₁ + ρ ^ (e₁ + (d+1)) = ρ ^ e₁ * (1 + ρ ^ (d+1)) := by
  rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]

theorem sum_shape {S a' q : Nat} (hdiv : 2 ^ (a'+1) * q + 2 ^ a' = S) :
    S = 2 ^ a' * (2 * q + 1) := by
  have hexp : 2 ^ a' * (2 * q + 1) = 2 ^ (a'+1) * q + 2 ^ a' := by
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.pow_succ]
  omega

/-- The 2-adic admissibility condition of Theorem C, in terms of `a = v₂(b-1)`.
`a ≠ 1` is Theorem B; the rest bites only at `a ≥ 3` with `e₂ - e₁` even. -/
def LiveTwoAdic (a e₁ e₂ : Nat) : Prop :=
  a ≠ 1 ∧ (a ≤ 2 ∨ (e₂ - e₁) % 2 = 1 ∨ e₁ ∣ (a - 1))

/-- **Theorem C, necessity.**  A residue exists only in the classes above.  The
argument is one valuation count: `ρ^e₁ + ρ^e₂ = ρ^e₁·(1 + ρ^(e₂-e₁))` must have
`v₂` exactly `a - 1`, and the three cases of `ρ` (zero, odd, even) supply the
three clauses. -/
theorem live_of_residue {b e₁ e₂ T a m ρ : Nat} (hb : 1 < b) (he₁ : 1 ≤ e₁) (hlt : e₁ < e₂)
    (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ a * m)
    (hρ : (ρ ^ e₁ + ρ ^ e₂) % (b - 1) = T % (b - 1)) :
    LiveTwoAdic a e₁ e₂ := by
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · exact ⟨by omega, Or.inl (by omega)⟩
  obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  subst ha'
  obtain ⟨d, hd⟩ : ∃ d, e₂ = e₁ + (d + 1) := ⟨e₂ - e₁ - 1, by omega⟩
  -- the sum is `2^(a-1)` times an odd number
  have h2A : 2 * (2 ^ a' * m) = b - 1 := by rw [hM, ← Nat.mul_assoc, ← Nat.pow_succ']
  have hdvd : 2 ^ (a' + 1) ∣ (b - 1) := ⟨m, hM⟩
  have hstep : ∀ x y : Nat, x % (b - 1) = y % (b - 1) → x % 2 ^ (a'+1) = y % 2 ^ (a'+1) := by
    intro x y hxy
    rw [← Nat.mod_mod_of_dvd x hdvd, ← Nat.mod_mod_of_dvd y hdvd, hxy]
  have hSA : (ρ ^ e₁ + ρ ^ e₂) % 2 ^ (a'+1) = 2 ^ a' := by
    rw [hstep _ _ (hρ.trans (target_eq hb hT h2A)), half_mod hm]
  have hSodd : ρ ^ e₁ + ρ ^ e₂ = 2 ^ a' * (2 * ((ρ ^ e₁ + ρ ^ e₂) / 2 ^ (a'+1)) + 1) := by
    refine sum_shape ?_
    have := Nat.div_add_mod (ρ ^ e₁ + ρ ^ e₂) (2 ^ (a'+1))
    omega
  have hUodd : (2 * ((ρ ^ e₁ + ρ ^ e₂) / 2 ^ (a'+1)) + 1) % 2 = 1 := by omega
  -- `ρ = 0` gives the sum `0`, which has no valuation at all
  rcases Nat.eq_zero_or_pos ρ with rfl | hρpos
  · have hz : (0:Nat) ^ e₁ + 0 ^ e₂ = 0 := by
      rw [Nat.zero_pow (by omega), Nat.zero_pow (by omega)]
    have hpos : 0 < 2 ^ a' * (2 * ((0 ^ e₁ + 0 ^ e₂) / 2 ^ (a'+1)) + 1) :=
      Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
    omega
  obtain ⟨w, u, hu, huodd⟩ := two_adic_split ρ hρpos
  rw [hd] at hSodd hUodd ⊢
  rw [sum_factor] at hSodd hUodd
  rcases Nat.eq_zero_or_pos w with rfl | hwpos
  · -- `ρ` odd
    have hρodd : ρ % 2 = 1 := by rw [hu] at *; simpa using huodd
    by_cases hpar : (d + 1) % 2 = 0
    · -- `e₂ - e₁` even: `ρ^(e₂-e₁) ≡ 1 (mod 4)`, so the valuation is exactly 1
      obtain ⟨k, hk⟩ : ∃ k, d + 1 = 2 * k := ⟨(d+1) / 2, by omega⟩
      have hpow4 : ρ ^ (d+1) % 4 = 1 := by
        rw [hk, Nat.pow_mul, pow_mod_one (odd_sq_mod_four hρodd) k]
      obtain ⟨t, ht⟩ : ∃ t, 1 + ρ ^ (d+1) = 2 * (2 * t + 1) := ⟨(ρ ^ (d+1) - 1) / 4, by omega⟩
      have hfac : ρ ^ e₁ * (1 + ρ ^ (d+1)) = 2 ^ 1 * (ρ ^ e₁ * (2 * t + 1)) := by
        rw [ht, Nat.pow_one, Nat.mul_left_comm]
      have hodd2 : (ρ ^ e₁ * (2 * t + 1)) % 2 = 1 := by
        rw [Nat.mul_mod, odd_pow hρodd e₁]
        omega
      have := two_pow_odd_unique hodd2 hUodd (hfac.symm.trans hSodd)
      exact ⟨by omega, Or.inl (by omega)⟩
    · -- `e₂ - e₁` odd: the valuation is unconstrained, but positive
      have hodd : ρ ^ (d+1) % 2 = 1 := odd_pow hρodd _
      obtain ⟨c, U, hcU, hUo⟩ := two_adic_split (1 + ρ ^ (d+1)) (by omega)
      have hcpos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with rfl | h
        · rw [Nat.pow_zero, Nat.one_mul] at hcU; omega
        · exact h
      have hfac : ρ ^ e₁ * (1 + ρ ^ (d+1)) = 2 ^ c * (ρ ^ e₁ * U) := by
        rw [hcU, Nat.mul_left_comm]
      have hodd2 : (ρ ^ e₁ * U) % 2 = 1 := by
        rw [Nat.mul_mod, odd_pow hρodd e₁, hUo]
      have := two_pow_odd_unique hodd2 hUodd (hfac.symm.trans hSodd)
      exact ⟨by omega, Or.inr (Or.inl (by omega))⟩
  · -- `ρ` even: `1 + ρ^(e₂-e₁)` is odd, so the valuation is `v₂(ρ)·e₁`
    have hρeven : ρ % 2 = 0 := by
      rw [hu]
      obtain ⟨p, hp⟩ : ∃ p, w = p + 1 := ⟨w - 1, by omega⟩
      rw [hp, Nat.pow_succ, Nat.mul_comm (2^p) 2, Nat.mul_assoc, Nat.mul_mod_right]
    have hcof : (1 + ρ ^ (d+1)) % 2 = 1 := by
      have := pow_mod_two (n := ρ) (d+1) (by omega)
      omega
    have hfac : ρ ^ e₁ * (1 + ρ ^ (d+1)) = 2 ^ (w * e₁) * (u ^ e₁ * (1 + ρ ^ (d+1))) := by
      rw [hu, Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]
    have hodd2 : (u ^ e₁ * (1 + ρ ^ (d+1))) % 2 = 1 := by
      rw [Nat.mul_mod, odd_pow huodd e₁, hcof]
    have hwe := two_pow_odd_unique hodd2 hUodd (hfac.symm.trans hSodd)
    have : 0 < w * e₁ := Nat.mul_pos hwpos (by omega)
    exact ⟨by omega, Or.inr (Or.inr ⟨w, by rw [Nat.mul_comm]; omega⟩)⟩

/-! ### §7.4  Theorem C -/

/--
**Theorem C.**  For every base `b > 1`, every pair `1 ≤ e₁ < e₂` and every
factorisation `b - 1 = 2^a·m` with `m` odd, the residue set is nonempty **iff**
`a ≠ 1` and one of `a ≤ 2`, `e₂ - e₁` odd, `e₁ ∣ a - 1` holds.

No odd prime divisor of `b-1` appears anywhere: the classification is a
condition on `v₂(b-1)` and the pair alone, which is why the dead bases form a
union of congruence classes mod powers of two.
-/
theorem residues_nonempty_iff {b e₁ e₂ T a m : Nat} (hb : 1 < b) (he₁ : 1 ≤ e₁) (hlt : e₁ < e₂)
    (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ a * m) :
    (∃ ρ, (ρ ^ e₁ + ρ ^ e₂) % (b - 1) = T % (b - 1)) ↔ LiveTwoAdic a e₁ e₂ := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact live_of_residue hb he₁ hlt hm hT hM hρ
  · rintro ⟨hne, hcases⟩
    rcases Nat.lt_or_ge a 3 with hsmall | hbig
    · have ha : a = 0 ∨ a = 2 := by omega
      rcases ha with rfl | rfl
      · rw [Nat.pow_zero, Nat.one_mul] at hM
        exact ⟨0, residue_of_even_base hb he₁ (by omega) hT (by omega)⟩
      · exact ⟨m ^ 2, residue_of_two_adic_two hb he₁ (by omega) hm hT hM⟩
    · rcases hcases with h | h | h
      · omega
      · obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
        exact ⟨_, residue_of_odd_gap hb hm hT hM (by omega)⟩
      · obtain ⟨V, hV⟩ := h
        have hVpos : 1 ≤ V := by
          rcases Nat.eq_zero_or_pos V with rfl | h'
          · omega
          · exact h'
        have hMV : b - 1 = 2 ^ (V * e₁ + 1) * m := by
          rw [hM, Nat.mul_comm V e₁]
          have hidx : e₁ * V + 1 = a := by omega
          rw [hidx]
        exact ⟨_, residue_of_dvd hb he₁ hlt hVpos hm hT hMV⟩

/-- **Theorem C, dead form** — the classification read as a list of dead classes,
which is how §4 of the report states it. -/
theorem residues_empty_iff {b e₁ e₂ T a m : Nat} (hb : 1 < b) (he₁ : 1 ≤ e₁) (hlt : e₁ < e₂)
    (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ a * m) :
    (∀ ρ, (ρ ^ e₁ + ρ ^ e₂) % (b - 1) ≠ T % (b - 1))
      ↔ (a = 1 ∨ (3 ≤ a ∧ (e₂ - e₁) % 2 = 0 ∧ ¬ e₁ ∣ (a - 1))) := by
  have hiff := residues_nonempty_iff hb he₁ hlt hm hT hM
  constructor
  · intro hall
    have hnot : ¬ LiveTwoAdic a e₁ e₂ := fun hl => (hiff.2 hl).elim (fun ρ hρ => hall ρ hρ)
    by_cases h1 : a = 1
    · exact Or.inl h1
    by_cases h2 : a ≤ 2
    · exact absurd ⟨h1, Or.inl h2⟩ hnot
    by_cases h3 : (e₂ - e₁) % 2 = 1
    · exact absurd ⟨h1, Or.inr (Or.inl h3)⟩ hnot
    by_cases h4 : e₁ ∣ (a - 1)
    · exact absurd ⟨h1, Or.inr (Or.inr h4)⟩ hnot
    exact Or.inr ⟨by omega, by omega, h4⟩
  · intro hdead ρ hρ
    obtain ⟨hne, hcases⟩ := live_of_residue hb he₁ hlt hm hT hM hρ
    rcases hdead with rfl | ⟨h3, hpar, hnd⟩
    · exact hne rfl
    · rcases hcases with h | h | h
      · omega
      · omega
      · exact hnd h

/-- The operative form: a base in a dead 2-adic class admits no `n` whose digit
sums satisfy the identity, hence no solution.  Same shape as
`no_nice_of_mod_four`, of which this is the generalisation. -/
theorem no_nice_of_two_adic {b e₁ e₂ a m n : Nat} (hb : 1 < b) (he₁ : 1 ≤ e₁) (hlt : e₁ < e₂)
    (hm : m % 2 = 1) (hM : b - 1 = 2 ^ a * m)
    (hdead : a = 1 ∨ (3 ≤ a ∧ (e₂ - e₁) % 2 = 0 ∧ ¬ e₁ ∣ (a - 1)))
    (hT : 2 * (digitSum b (n ^ e₁) + digitSum b (n ^ e₂)) = b * (b - 1)) : False := by
  have hd1 : n ^ e₁ % (b-1) = digitSum b (n ^ e₁) % (b-1) := digitSum_mod hb _
  have hd2 : n ^ e₂ % (b-1) = digitSum b (n ^ e₂) % (b-1) := digitSum_mod hb _
  have hsum : (n ^ e₁ + n ^ e₂) % (b-1)
      = (digitSum b (n ^ e₁) + digitSum b (n ^ e₂)) % (b-1) := by
    rw [Nat.add_mod, hd1, hd2, ← Nat.add_mod]
  exact (residues_empty_iff hb he₁ hlt hm hT hM).2 hdead n hsum

/-! ### §7.5  Non-vacuity, and the theorem firing

The `(2,4)` pair at base 17 is the sharpest example available: `17 % 3 = 2` so
Theorem A says nothing, `17 % 4 = 1` so Theorem B says nothing, and
`N(2,4) = 12` with `17 ∤ 12` so Theorem G says nothing.  `v₂(16) = 4`, the gap
`4 - 2 = 2` is even and `2 ∤ 3`, so Theorem C alone kills it.  Base 33 — the very
next base with `v₂(b-1) ≥ 3` that A leaves alive — is *not* killed, and the
witness is exhibited, so the boundary `e₁ ∣ a-1` is sharp and not slack. -/

/-- `(2,4)` in base 17: no residue at all.  `T = 136`, `2·136 = 17·16`. -/
theorem two_four_base_seventeen_dead (ρ : Nat) : (ρ ^ 2 + ρ ^ 4) % 16 ≠ 136 % 16 :=
  (residues_empty_iff (b := 17) (a := 4) (m := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).2 (Or.inr ⟨by decide, by decide, by decide⟩) ρ

/-- ...and base 33 is alive, with the witness `ρ = 2^2·1 = 4` the theorem
predicts: `v₂(32) = 5` and `e₁ = 2 ∣ 4`. -/
theorem two_four_base_thirtythree_live : (4 ^ 2 + 4 ^ 4) % 32 = 528 % 32 := by decide

/-- Base 10 had better be alive, or the theorem would contradict 69.
`v₂(9) = 0`, so the `a = 0` clause applies and `ρ = 0` is a residue — as is 69
itself, which is the residue the solution actually lives in. -/
theorem base_ten_live : LiveTwoAdic 0 2 3 := ⟨by decide, Or.inl (by decide)⟩

theorem base_ten_residue : (69 ^ 2 + 69 ^ 3) % 9 = 45 % 9 := by decide

/-- Theorem B is the `a = 1` case: `b ≡ 3 (mod 4)` is exactly `v₂(b-1) = 1`.
Re-deriving `residues_empty_of_mod_four` from Theorem C, for every pair. -/
theorem residues_empty_of_mod_four_of_C {b e₁ e₂ T ρ : Nat}
    (hb : 1 < b) (he₁ : 1 ≤ e₁) (hlt : e₁ < e₂) (hmod : b % 4 = 3)
    (hT : 2 * T = b * (b - 1)) :
    (ρ ^ e₁ + ρ ^ e₂) % (b - 1) ≠ T % (b - 1) := by
  refine (residues_empty_iff (a := 1) (m := (b-1)/2) hb he₁ hlt (by omega) hT ?_).2
    (Or.inl rfl) ρ
  rw [Nat.pow_one]
  omega

/-! ### §7.6  The single-exponent family

`n^e` alone pandigital is the `E = e` member of the family, and §13 of the
report recommends it as the best compute target — which makes "which bases are
live" load-bearing there.  The same valuation count answers it, and more simply,
because `v₂(ρ^e) = e·v₂(ρ)` with no cofactor `1 + ρ^d` to think about:

> `R_b = ∅`  ⟺  `a ≥ 1` and `e ∤ a - 1`.

Note `a = 1` is **live** here — Theorem B needs the sum `ρ^e₁ + ρ^e₂ ≡ 2ρ`, and a
single exponent has no partner to pair with — which is why `b ≡ 3 (mod 4)`
survives for `n^4` and not for `(1,3)`. -/

/-- `a - 1 = e·V` (including `V = 0`, i.e. `a = 1`): `ρ = 2^V·m`. -/
theorem residue_single_of_dvd {b e T m V : Nat} (hb : 1 < b) (he : 1 ≤ e) (hm : m % 2 = 1)
    (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ (V * e + 1) * m) :
    (2 ^ V * m) ^ e % (b - 1) = T % (b - 1) := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  refine residue_of_odd_cofactor (w := V * (f+1)) (m := m) (W := m ^ f) hb hT hM
    (odd_pow hm f) ?_
  rw [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_succ (m := f), Nat.mul_comm (m ^ f) m]

/-- `a = 0`, i.e. `b` even: `ρ = 0`. -/
theorem residue_single_of_even_base {b e T : Nat} (hb : 1 < b) (he : 1 ≤ e)
    (hT : 2 * T = b * (b - 1)) (hbe : b % 2 = 0) : (0:Nat) ^ e % (b - 1) = T % (b - 1) := by
  rw [Nat.zero_pow (by omega), target_zero hb hT hbe]
  simp

/-- **Theorem C, single-exponent form.**  (`a - 1` is truncated subtraction, so
the `a = 0` disjunct is formally implied by the second; it is kept because the
mathematics has two cases — even base, and `v₂(b-1) ≡ 1 mod e` — not one.) -/
theorem residues_single_nonempty_iff {b e T a m : Nat} (hb : 1 < b) (he : 1 ≤ e)
    (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ a * m) :
    (∃ ρ, ρ ^ e % (b - 1) = T % (b - 1)) ↔ (a = 0 ∨ e ∣ (a - 1)) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · exact Or.inl rfl
    obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    subst ha'
    have h2A : 2 * (2 ^ a' * m) = b - 1 := by rw [hM, ← Nat.mul_assoc, ← Nat.pow_succ']
    have hdvd : 2 ^ (a' + 1) ∣ (b - 1) := ⟨m, hM⟩
    have hstep : ∀ x y : Nat, x % (b - 1) = y % (b - 1) → x % 2 ^ (a'+1) = y % 2 ^ (a'+1) := by
      intro x y hxy
      rw [← Nat.mod_mod_of_dvd x hdvd, ← Nat.mod_mod_of_dvd y hdvd, hxy]
    have hSA : ρ ^ e % 2 ^ (a'+1) = 2 ^ a' := by
      rw [hstep _ _ (hρ.trans (target_eq hb hT h2A)), half_mod hm]
    have hSodd : ρ ^ e = 2 ^ a' * (2 * (ρ ^ e / 2 ^ (a'+1)) + 1) := by
      refine sum_shape ?_
      have := Nat.div_add_mod (ρ ^ e) (2 ^ (a'+1))
      omega
    have hUodd : (2 * (ρ ^ e / 2 ^ (a'+1)) + 1) % 2 = 1 := by omega
    rcases Nat.eq_zero_or_pos ρ with rfl | hρpos
    · have hz : (0:Nat) ^ e = 0 := Nat.zero_pow (by omega)
      have hpos : 0 < 2 ^ a' * (2 * ((0:Nat) ^ e / 2 ^ (a'+1)) + 1) :=
        Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
      omega
    obtain ⟨w, u, hu, huodd⟩ := two_adic_split ρ hρpos
    have hfac : ρ ^ e = 2 ^ (w * e) * u ^ e := by rw [hu, Nat.mul_pow, ← Nat.pow_mul]
    have hwe := two_pow_odd_unique (odd_pow huodd e) hUodd (hfac.symm.trans hSodd)
    exact Or.inr ⟨w, by rw [Nat.mul_comm]; omega⟩
  · intro h
    rcases h with rfl | ⟨V, hV⟩
    · rw [Nat.pow_zero, Nat.one_mul] at hM
      exact ⟨0, residue_single_of_even_base hb he hT (by omega)⟩
    · rcases Nat.eq_zero_or_pos a with rfl | hapos
      · rw [Nat.pow_zero, Nat.one_mul] at hM
        exact ⟨0, residue_single_of_even_base hb he hT (by omega)⟩
      · refine ⟨2 ^ V * m, residue_single_of_dvd hb he hm hT ?_⟩
        rw [hM, Nat.mul_comm V e]
        have hidx : e * V + 1 = a := by omega
        rw [hidx]

/-- `n⁴` in base 29 has no residue: `v₂(28) = 2` and `4 ∤ 1`.  This is one of the
bases §13 of the report lists as killed, and base 8 — where the only known
solution `42⁴` lives — is even, hence `a = 0`, hence live. -/
theorem single_four_base_twentynine_dead (ρ : Nat) : ρ ^ 4 % 28 ≠ 406 % 28 := by
  intro h
  rcases (residues_single_nonempty_iff (b := 29) (e := 4) (a := 2) (m := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide)).1 ⟨ρ, h⟩ with h' | h' <;>
    revert h' <;> decide

/-- ...and base 33 is live, with the residue `2^1·1 = 2` the theorem predicts:
`v₂(32) = 5` and `4 ∣ 4`. -/
theorem single_four_base_thirtythree_live : (2:Nat) ^ 4 % 32 = 528 % 32 := by decide

/-! ## §8  Theorem F — the `2/E` greedy construction

`n mod b^(i+1)` pins digit `i` of `n^e₁` *and* digit `i` of `n^e₂`: two slots per
digit of `n`, the conservation law the whole repository runs on.  Theorem F turns
that budget into a construction.  Build `n` from the bottom; at level `i` the new
digit `x` moves each of the two slots along an arithmetic progression, and if the
common differences are units the progressions are bijections, so each already-used
value kills at most one `x` and the two progressions collide at most once.  With
`|Used| = 2i` that is `4i + 2` losses out of `b` choices, and `i ≤ d-1 ≈ b/E - 1`.

The output is a `d`-digit `n` whose `2d` low slots are pairwise distinct, hence a
digit deficiency of at most `b - 2d ≈ b(1 - 2/E)`. -/

/-! ### §8.0  Digit slots -/

/-- Digit `i` of `x` in base `b`, counting from the least significant. -/
def slot (b i x : Nat) : Nat := x / b ^ i % b

theorem slot_lt {b : Nat} (hb : 0 < b) (i x : Nat) : slot b i x < b := Nat.mod_lt _ hb

theorem slot_zero (b x : Nat) : slot b 0 x = x % b := by
  show x / b ^ 0 % b = x % b
  rw [Nat.pow_zero, Nat.div_one]

/-- A slot sees only the low `i+1` digits: this is the p-adic boundary, stated. -/
theorem slot_of_mod {b i x y : Nat} (h : x % b ^ (i + 1) = y % b ^ (i + 1)) :
    slot b i x = slot b i y := by
  have hp : b ^ (i + 1) = b ^ i * b := Nat.pow_succ b i
  show x / b ^ i % b = y / b ^ i % b
  rw [← Nat.mod_mul_right_div_self x (b ^ i) b, ← Nat.mod_mul_right_div_self y (b ^ i) b,
      ← hp, h]

/-- Hence `n mod b^(i+1)` pins slot `i` of `n^e` — two slots per digit of `n`. -/
theorem slot_pow_of_mod {b i x y e : Nat} (h : x % b ^ (i + 1) = y % b ^ (i + 1)) :
    slot b i (x ^ e) = slot b i (y ^ e) := by
  refine slot_of_mod ?_
  rw [Nat.pow_mod, h, ← Nat.pow_mod]

/-- Every slot below the digit count really is one of the digits. -/
theorem slot_mem_digits {b : Nat} (hb : 1 < b) :
    ∀ x i, i < numDigits b x → slot b i x ∈ digits b x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro i hi
    have hx : 0 < x := by
      rcases Nat.eq_zero_or_pos x with rfl | h
      · rw [numDigits_zero] at hi; omega
      · exact h
    have hnum : numDigits b x = numDigits b (x / b) + 1 := by
      rw [numDigits, dif_pos ⟨hb, hx⟩]
    rw [digits_step hb hx]
    match i with
    | 0 => rw [slot_zero]; exact List.Mem.head _
    | (j + 1) =>
      have hd : slot b (j + 1) x = slot b j (x / b) := by
        show x / b ^ (j + 1) % b = x / b / b ^ j % b
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (b ^ j) b]
      rw [hd]
      exact List.Mem.tail _ (ih (x / b) (Nat.div_lt_self hx hb) j (by omega))

/-! ### §8.1  The digit ladder

`(r + x·bⁱ)^e ≡ r^e + e·r^(e-1)·x·bⁱ (mod b^(i+1))` for `i ≥ 1`: every binomial
term from `x²b^{2i}` up is divisible by `b^(i+1)`, because `2i ≥ i+1`.  This is the
same recurrence the CUDA and Vulkan kernels advance the digit with. -/

theorem add_pow_ladder {b i : Nat} (hi : 1 ≤ i) (r x : Nat) : ∀ e,
    (r + x * b ^ i) ^ e % b ^ (i + 1)
      = (r ^ e + e * r ^ (e - 1) * x * b ^ i) % b ^ (i + 1) := by
  obtain ⟨c, hc⟩ : ∃ c, b ^ i * b ^ i = b ^ (i + 1) * c := by
    refine ⟨b ^ (i - 1), ?_⟩
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  intro e
  induction e with
  | zero => simp
  | succ e ih =>
    match e with
    | 0 => simp
    | (e' + 1) =>
      -- `E = e'+1 ≥ 1`, so `r^(E-1) * r = r^E` and the cross term is a genuine
      -- multiple of `bⁱ·bⁱ`.
      have key : (r ^ (e' + 1) + (e' + 1) * r ^ e' * x * b ^ i) * (r + x * b ^ i)
          = (r ^ (e' + 2) + (e' + 2) * r ^ (e' + 1) * x * b ^ i)
            + ((e' + 1) * r ^ e' * x * x) * (b ^ i * b ^ i) := by
        have hr : r ^ (e' + 2) = r ^ (e' + 1) * r := by rw [Nat.pow_succ]
        have hr' : r ^ (e' + 1) = r ^ e' * r := by rw [Nat.pow_succ]
        rw [hr, hr']
        simp only [Nat.add_mul, Nat.mul_add, Nat.succ_mul]
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
      have hmul : (e' + 1) * r ^ e' * x * x * (b ^ i * b ^ i)
          = b ^ (i + 1) * ((e' + 1) * r ^ e' * x * x * c) := by
        rw [hc]; exact Nat.mul_left_comm _ _ _
      calc (r + x * b ^ i) ^ (e' + 2) % b ^ (i + 1)
          = (r + x * b ^ i) ^ (e' + 1) % b ^ (i + 1) * ((r + x * b ^ i) % b ^ (i + 1))
              % b ^ (i + 1) := by rw [Nat.pow_succ, Nat.mul_mod]
        _ = (r ^ (e' + 1) + (e' + 1) * r ^ e' * x * b ^ i) % b ^ (i + 1)
              * ((r + x * b ^ i) % b ^ (i + 1)) % b ^ (i + 1) := by
              rw [show (e' + 1) - 1 = e' from rfl] at ih; rw [ih]
        _ = (r ^ (e' + 1) + (e' + 1) * r ^ e' * x * b ^ i) * (r + x * b ^ i)
              % b ^ (i + 1) := by rw [← Nat.mul_mod]
        _ = ((r ^ (e' + 2) + (e' + 2) * r ^ (e' + 1) * x * b ^ i)
              + b ^ (i + 1) * ((e' + 1) * r ^ e' * x * x * c)) % b ^ (i + 1) := by
              rw [key, hmul]
        _ = (r ^ (e' + 2) + (e' + 2) * r ^ (e' + 1) * x * b ^ i) % b ^ (i + 1) :=
              Nat.add_mul_mod_self_left _ _ _

/-- The ladder as the greedy uses it: adding digit `x` at level `i` moves slot `i`
of `n^e` along the progression with common difference `e·r^(e-1) (mod b)`. -/
theorem slot_step {b i : Nat} (hb : 0 < b) (hi : 1 ≤ i) (r x e : Nat) :
    slot b i ((r + x * b ^ i) ^ e) = (slot b i (r ^ e) + e * r ^ (e - 1) * x) % b := by
  have hstep : slot b i ((r + x * b ^ i) ^ e)
      = slot b i (r ^ e + e * r ^ (e - 1) * x * b ^ i) := slot_of_mod (add_pow_ladder hi r x e)
  have hbi : 0 < b ^ i := Nat.pow_pos hb
  rw [hstep]
  show (r ^ e + e * r ^ (e - 1) * x * b ^ i) / b ^ i % b = (r ^ e / b ^ i % b + _) % b
  rw [Nat.mul_comm (e * r ^ (e - 1) * x) (b ^ i), Nat.add_mul_div_left _ _ hbi,
      Nat.mod_add_mod]

/-! ### §8.2  Two injectivity lemmas

The progressions are bijections when their common differences are units, and the
*difference* of the two progressions is a bijection when `α₁ - α₂` is — which is
the side condition Theorem F carries, here supplied as an explicit unit `β`. -/

/-- Cancelling a common summand under `%`. -/
theorem mod_add_cancel {b c u v : Nat} (hb : 0 < b) (h : (u + c) % b = (v + c) % b) :
    u % b = v % b := by
  rcases Nat.le_total u v with hle | hle
  · have h1 : u + c ≤ v + c := by omega
    have hd : b ∣ v + c - (u + c) := (dvd_sub_iff_mod_eq hb h1).mpr h.symm
    have he : v + c - (u + c) = v - u := by omega
    rw [he] at hd
    exact ((dvd_sub_iff_mod_eq hb hle).mp hd).symm
  · have h1 : v + c ≤ u + c := by omega
    have hd : b ∣ u + c - (v + c) := (dvd_sub_iff_mod_eq hb h1).mpr h
    have he : u + c - (v + c) = u - v := by omega
    rw [he] at hd
    exact (dvd_sub_iff_mod_eq hb hle).mp hd

/-- `x ↦ (A + α·x) mod b` is injective on `{0,…,b-1}` when `α` is a unit. -/
theorem lin_inj {b α A x y : Nat} (hb : 0 < b) (hα : Nat.Coprime b α)
    (hx : x < b) (hy : y < b) (h : (A + α * x) % b = (A + α * y) % b) : x = y := by
  rcases Nat.le_total x y with hle | hle
  · obtain ⟨t, rfl⟩ : ∃ t, y = x + t := ⟨y - x, by omega⟩
    have hmul : α * (x + t) = α * x + α * t := Nat.mul_add α x t
    have h1 : A + α * x ≤ A + α * (x + t) := by omega
    have hd : b ∣ A + α * (x + t) - (A + α * x) :=
      (dvd_sub_iff_mod_eq hb h1).mpr h.symm
    have he : A + α * (x + t) - (A + α * x) = α * t := by omega
    rw [he] at hd
    have ht : t = 0 := Nat.eq_zero_of_dvd_of_lt (hα.dvd_of_dvd_mul_left hd) (by omega)
    omega
  · obtain ⟨t, rfl⟩ : ∃ t, x = y + t := ⟨x - y, by omega⟩
    have hmul : α * (y + t) = α * y + α * t := Nat.mul_add α y t
    have h1 : A + α * y ≤ A + α * (y + t) := by omega
    have hd : b ∣ A + α * (y + t) - (A + α * y) :=
      (dvd_sub_iff_mod_eq hb h1).mpr h
    have he : A + α * (y + t) - (A + α * y) = α * t := by omega
    rw [he] at hd
    have ht : t = 0 := Nat.eq_zero_of_dvd_of_lt (hα.dvd_of_dvd_mul_left hd) (by omega)
    omega

/-- The two progressions collide for at most one digit `x`.  This is the side
condition of Theorem F: `α₁ - α₂` must be a unit, supplied as `β` with
`α₂ + β ≡ α₁`. -/
theorem clash_inj {b α₁ α₂ β A₁ A₂ x y : Nat} (hb : 0 < b) (hβ : Nat.Coprime b β)
    (hsep : (α₂ + β) % b = α₁ % b) (hx : x < b) (hy : y < b)
    (h₁ : (A₁ + α₁ * x) % b = (A₂ + α₂ * x) % b)
    (h₂ : (A₁ + α₁ * y) % b = (A₂ + α₂ * y) % b) : x = y := by
  -- add the two collision equations, so that `A₁`, `A₂` cancel
  have hsum : (A₁ + α₁ * x + (A₂ + α₂ * y)) % b = (A₂ + α₂ * x + (A₁ + α₁ * y)) % b := by
    rw [Nat.add_mod, h₁, ← h₂, ← Nat.add_mod]
  have hcomm₁ : A₁ + α₁ * x + (A₂ + α₂ * y) = α₁ * x + α₂ * y + (A₁ + A₂) := by omega
  have hcomm₂ : A₂ + α₂ * x + (A₁ + α₁ * y) = α₂ * x + α₁ * y + (A₁ + A₂) := by omega
  rw [hcomm₁, hcomm₂] at hsum
  have hcancel : (α₁ * x + α₂ * y) % b = (α₂ * x + α₁ * y) % b := mod_add_cancel hb hsum
  -- replace `α₁` by `α₂ + β`
  have hsub : ∀ z, (α₁ * z) % b = (α₂ * z + β * z) % b := by
    intro z
    rw [Nat.mul_mod, ← hsep, ← Nat.mul_mod, Nat.add_mul]
  have hL : (α₁ * x + α₂ * y) % b = (α₂ * x + α₂ * y + β * x) % b := by
    rw [Nat.add_mod, hsub x, ← Nat.add_mod]
    congr 1
    omega
  have hR : (α₂ * x + α₁ * y) % b = (α₂ * x + α₂ * y + β * y) % b := by
    rw [Nat.add_mod, hsub y, ← Nat.add_mod]
    congr 1
    omega
  rw [hL, hR] at hcancel
  have hL' : α₂ * x + α₂ * y + β * x = β * x + (α₂ * x + α₂ * y) := by omega
  have hR' : α₂ * x + α₂ * y + β * y = β * y + (α₂ * x + α₂ * y) := by omega
  rw [hL', hR'] at hcancel
  have hfin : (β * x) % b = (β * y) % b := mod_add_cancel hb hcancel
  exact lin_inj (A := 0) hb hβ hx hy (by rw [Nat.zero_add, Nat.zero_add]; exact hfin)

/-! ### §8.3  Counting

Core has `List.countP` but not the four facts the pigeonhole needs, so they are
proved here.  `memb` is a decidable membership test that reduces in the kernel,
in the style of `occ` in §5. -/

/-- Membership as a `Bool`, so it can be counted. -/
def memb (v : Nat) : List Nat → Bool
  | [] => false
  | a :: l => (a == v) || memb v l

theorem memb_nil (v : Nat) : memb v [] = false := rfl

theorem memb_cons (v a : Nat) (l : List Nat) :
    memb v (a :: l) = ((a == v) || memb v l) := rfl

theorem memb_iff (v : Nat) : ∀ l : List Nat, memb v l = true ↔ v ∈ l := by
  intro l
  induction l with
  | nil => rw [memb_nil]; simp
  | cons a t ih =>
    rw [memb_cons, List.mem_cons, Bool.or_eq_true, beq_iff_eq, ih]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

theorem countP_or_le (p q : Nat → Bool) : ∀ l : List Nat,
    List.countP (fun a => p a || q a) l ≤ List.countP p l + List.countP q l := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    by_cases hp : p a = true <;> by_cases hq : q a = true <;> simp [hp, hq] <;> omega

/-- A predicate that can hold at only one element of a duplicate-free list is
counted at most once. -/
theorem countP_le_one {p : Nat → Bool} : ∀ l : List Nat, l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, p x = true → p y = true → x = y) → List.countP p l ≤ 1 := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
    intro hnd huniq
    rw [List.nodup_cons] at hnd
    rw [List.countP_cons]
    by_cases hpa : p a = true
    · have hzero : List.countP p t = 0 := by
        refine List.countP_eq_zero.mpr ?_
        intro y hy hpy
        have : y = a := huniq y (List.Mem.tail _ hy) a (List.Mem.head _) hpy hpa
        exact hnd.1 (this ▸ hy)
      simp [hpa, hzero]
    · have := ih hnd.2 (fun x hx y hy => huniq x (List.Mem.tail _ hx) y (List.Mem.tail _ hy))
      simp [hpa]
      omega

/-- If `f` is injective on `l`, at most `U.length` of `l`'s elements land in `U`. -/
theorem countP_memb_le {f : Nat → Nat} {l : List Nat} (hl : l.Nodup)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    ∀ U : List Nat, List.countP (fun x => memb (f x) U) l ≤ U.length := by
  intro U
  induction U with
  | nil =>
    have : List.countP (fun x => memb (f x) ([] : List Nat)) l = 0 :=
      List.countP_eq_zero.mpr (fun a _ h => by simp [memb] at h)
    omega
  | cons u U' ih =>
    have hsplit : ∀ x : Nat, memb (f x) (u :: U') = ((f x == u) || memb (f x) U') := by
      intro x
      rw [memb_cons]
      by_cases h : u = f x
      · rw [h]
      · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]
    have hrw : List.countP (fun x => memb (f x) (u :: U')) l
        = List.countP (fun x => (f x == u) || memb (f x) U') l := by
      refine List.countP_congr ?_
      intro x _
      rw [hsplit x]
    have hone : List.countP (fun x => f x == u) l ≤ 1 := by
      refine countP_le_one l hl ?_
      intro x hx y hy hpx hpy
      exact hinj x hx y hy (by simp at hpx hpy; rw [hpx, hpy])
    have := countP_or_le (fun x => f x == u) (fun x => memb (f x) U') l
    simp only [List.length_cons]
    omega

theorem countP_split (p : Nat → Bool) : ∀ l : List Nat,
    List.countP p l + List.countP (fun a => !p a) l = l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.length_cons]
    by_cases hp : p a = true <;> simp [hp] <;> omega

theorem exists_of_countP_pos {p : Nat → Bool} : ∀ l : List Nat, 0 < List.countP p l →
    ∃ a, a ∈ l ∧ p a = true := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    rw [List.countP_cons] at h
    by_cases hp : p a = true
    · exact ⟨a, List.Mem.head _, hp⟩
    · simp only [hp] at h
      obtain ⟨y, hy, hpy⟩ := ih h
      exact ⟨y, List.Mem.tail _ hy, hpy⟩

theorem countP_eq_length_filter (p : Nat → Bool) : ∀ l : List Nat,
    List.countP p l = (l.filter p).length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.filter_cons]
    by_cases hp : p a = true <;> simp [hp, ih]

/-! ### §8.4  One greedy step

At most `2|U| + 2` of the `b` digits are lost: `|U|` to each progression hitting an
already-used value, one to the two progressions colliding, and one to the leading
digit having to be nonzero. -/

/-- The pigeonhole, over abstract slot maps: two maps injective on `{0,…,b-1}`
whose coincidence set has at most one element leave a nonzero digit avoiding `U`
in both, as soon as `2|U| + 2 < b`. -/
theorem exists_good_digit {b : Nat} (hb : 0 < b) (s₁ s₂ : Nat → Nat)
    (hinj₁ : ∀ x, x < b → ∀ y, y < b → s₁ x = s₁ y → x = y)
    (hinj₂ : ∀ x, x < b → ∀ y, y < b → s₂ x = s₂ y → x = y)
    (hclash : ∀ x, x < b → ∀ y, y < b → s₁ x = s₂ x → s₁ y = s₂ y → x = y)
    (U : List Nat) (hcount : 2 * U.length + 2 < b) :
    ∃ x, 0 < x ∧ x < b ∧ s₁ x ∉ U ∧ s₂ x ∉ U ∧ s₁ x ≠ s₂ x := by
  have hrange : ∀ x ∈ List.range b, x < b := fun x hx => List.mem_range.mp hx
  -- each of the four losses is bounded
  have hz : List.countP (fun x => x == 0) (List.range b) ≤ 1 := by
    refine countP_le_one _ List.nodup_range ?_
    intro x _ y _ hx hy
    simp only [beq_iff_eq] at hx hy
    omega
  have hm₁ : List.countP (fun x => memb (s₁ x) U) (List.range b) ≤ U.length :=
    countP_memb_le List.nodup_range
      (fun x hx y hy h => hinj₁ x (hrange x hx) y (hrange y hy) h) U
  have hm₂ : List.countP (fun x => memb (s₂ x) U) (List.range b) ≤ U.length :=
    countP_memb_le List.nodup_range
      (fun x hx y hy h => hinj₂ x (hrange x hx) y (hrange y hy) h) U
  have hc : List.countP (fun x => s₁ x == s₂ x) (List.range b) ≤ 1 := by
    refine countP_le_one _ List.nodup_range ?_
    intro x hx y hy hpx hpy
    simp only [beq_iff_eq] at hpx hpy
    exact hclash x (hrange x hx) y (hrange y hy) hpx hpy
  -- so the bad digits do not exhaust the base
  have hsum₁ := countP_or_le (fun x => (x == 0) || memb (s₁ x) U)
      (fun x => memb (s₂ x) U || (s₁ x == s₂ x)) (List.range b)
  have hsum₂ := countP_or_le (fun x => x == 0) (fun x => memb (s₁ x) U) (List.range b)
  have hsum₃ := countP_or_le (fun x => memb (s₂ x) U) (fun x => s₁ x == s₂ x) (List.range b)
  have hlen : (List.range b).length = b := List.length_range
  have hsplit := countP_split
    (fun x => ((x == 0) || memb (s₁ x) U) || (memb (s₂ x) U || (s₁ x == s₂ x)))
    (List.range b)
  have hpos : 0 < List.countP
      (fun x => !(((x == 0) || memb (s₁ x) U) || (memb (s₂ x) U || (s₁ x == s₂ x))))
      (List.range b) := by omega
  obtain ⟨x, hxmem, hxbad⟩ := exists_of_countP_pos _ hpos
  have hxb : x < b := hrange x hxmem
  simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hxbad
  obtain ⟨⟨hx0, hu₁⟩, hu₂, hne⟩ := hxbad
  refine ⟨x, Nat.pos_of_ne_zero hx0, hxb, ?_, ?_, hne⟩
  · intro hmem
    rw [(memb_iff _ U).mpr hmem] at hu₁
    exact Bool.noConfusion hu₁
  · intro hmem
    rw [(memb_iff _ U).mpr hmem] at hu₂
    exact Bool.noConfusion hu₂

/-! ### §8.5  The greedy induction

The invariant carried up the levels: `r` has exactly `i` digits, its last digit is
the chosen unit `ρ` (so every progression's common difference stays the same), and
`U` is the list of the `2i` slot values already placed — pairwise distinct, all
`< b`, and each genuinely a slot of `r^e₁` or of `r^e₂`. -/

/-- The greedy state after `i` levels. -/
def GreedyInv (b e₁ e₂ ρ i r : Nat) (U : List Nat) : Prop :=
  b ^ (i - 1) ≤ r ∧ r < b ^ i ∧ r % b = ρ ∧
  U.length = 2 * i ∧ U.Nodup ∧ (∀ v ∈ U, v < b) ∧
  (∀ v ∈ U, ∃ j, j < i ∧ (v = slot b j (r ^ e₁) ∨ v = slot b j (r ^ e₂)))

/-- Level 0: the starting digit `ρ`, whose two slots already differ. -/
theorem greedy_base {b e₁ e₂ ρ : Nat} (hb : 1 < b) (hρ : 0 < ρ) (hρb : ρ < b)
    (hstart : ρ ^ e₁ % b ≠ ρ ^ e₂ % b) :
    GreedyInv b e₁ e₂ ρ 1 ρ [ρ ^ e₁ % b, ρ ^ e₂ % b] := by
  refine ⟨?_, ?_, Nat.mod_eq_of_lt hρb, rfl, ?_, ?_, ?_⟩
  · rw [show (1 : Nat) - 1 = 0 from rfl, Nat.pow_zero]; omega
  · rw [Nat.pow_one]; exact hρb
  · rw [List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, List.nodup_nil⟩
    · intro h
      rcases List.mem_singleton.mp h with h'
      exact hstart h'
    · intro h; cases h
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact Nat.mod_lt _ (by omega)
    · rcases List.mem_singleton.mp hv' with rfl
      exact Nat.mod_lt _ (by omega)
  · intro v hv
    refine ⟨0, by omega, ?_⟩
    rw [slot_zero, slot_zero]
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact Or.inl rfl
    · rcases List.mem_singleton.mp hv' with rfl
      exact Or.inr rfl

/-- One level of the greedy.  `4i + 2 < b` is the whole content: `2i` used values,
each killing at most one digit in each of the two progressions, plus the one digit
where the progressions collide and the one that would make the leading digit `0`. -/
theorem greedy_step {b e₁ e₂ ρ β i r : Nat} (hb : 1 < b)
    (hce₁ : Nat.Coprime b e₁) (hce₂ : Nat.Coprime b e₂) (hcρ : Nat.Coprime b ρ)
    (hβ : Nat.Coprime b β)
    (hsep : (e₂ * ρ ^ (e₂ - 1) + β) % b = e₁ * ρ ^ (e₁ - 1) % b)
    (hi : 1 ≤ i) (hcount : 4 * i + 2 < b)
    (U : List Nat) (hinv : GreedyInv b e₁ e₂ ρ i r U) :
    ∃ r' U', GreedyInv b e₁ e₂ ρ (i + 1) r' U' := by
  obtain ⟨hlo, hhi, hmod, hlen, hnd, hltb, hslot⟩ := hinv
  have hb0 : 0 < b := by omega
  have hbi : 0 < b ^ i := Nat.pow_pos hb0
  -- the last digit of `r` is `ρ`, so `r` is a unit and the two common differences
  -- are the ones `hsep` speaks about
  have hcr : Nat.Coprime b r := by
    have hg : Nat.gcd b r = Nat.gcd ρ b := by rw [Nat.gcd_rec b r, hmod]
    show Nat.gcd b r = 1
    rw [hg]
    exact Nat.coprime_comm.mp hcρ
  have hα : ∀ e : Nat, (e * r ^ (e - 1)) % b = (e * ρ ^ (e - 1)) % b := by
    intro e
    rw [Nat.mul_mod, Nat.pow_mod, hmod, ← Nat.mul_mod]
  have hcα₁ : Nat.Coprime b (e₁ * r ^ (e₁ - 1)) := hce₁.mul_right (hcr.pow_right _)
  have hcα₂ : Nat.Coprime b (e₂ * r ^ (e₂ - 1)) := hce₂.mul_right (hcr.pow_right _)
  have hsep' : (e₂ * r ^ (e₂ - 1) + β) % b = e₁ * r ^ (e₁ - 1) % b := by
    rw [Nat.add_mod, hα e₂, ← Nat.add_mod, hsep, ← hα e₁]
  -- the pigeonhole picks the next digit
  obtain ⟨x, hx0, hxb, hxu₁, hxu₂, hxne⟩ :=
    exists_good_digit hb0
      (fun x => (slot b i (r ^ e₁) + e₁ * r ^ (e₁ - 1) * x) % b)
      (fun x => (slot b i (r ^ e₂) + e₂ * r ^ (e₂ - 1) * x) % b)
      (fun x hx y hy h => lin_inj hb0 hcα₁ hx hy h)
      (fun x hx y hy h => lin_inj hb0 hcα₂ hx hy h)
      (fun x hx y hy h₁ h₂ => clash_inj hb0 hβ hsep' hx hy h₁ h₂)
      U (by omega)
  refine ⟨r + x * b ^ i,
    slot b i ((r + x * b ^ i) ^ e₁) :: slot b i ((r + x * b ^ i) ^ e₂) :: U, ?_⟩
  -- the two new slots are exactly the two progression values
  have hs₁ : slot b i ((r + x * b ^ i) ^ e₁)
      = (slot b i (r ^ e₁) + e₁ * r ^ (e₁ - 1) * x) % b := slot_step hb0 hi r x e₁
  have hs₂ : slot b i ((r + x * b ^ i) ^ e₂)
      = (slot b i (r ^ e₂) + e₂ * r ^ (e₂ - 1) * x) % b := slot_step hb0 hi r x e₂
  -- the earlier slots are untouched: `r' ≡ r (mod b^(j+1))` for every `j < i`
  have hlow : ∀ j, j < i → ∀ e, slot b j ((r + x * b ^ i) ^ e) = slot b j (r ^ e) := by
    intro j hj e
    refine slot_pow_of_mod ?_
    obtain ⟨c, hc⟩ : ∃ c, b ^ i = b ^ (j + 1) * c :=
      ⟨b ^ (i - (j + 1)), by rw [← Nat.pow_add]; congr 1; omega⟩
    rw [hc, Nat.mul_left_comm]
    exact Nat.add_mul_mod_self_left _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : b ^ i = 1 * b ^ i := (Nat.one_mul _).symm
    rw [show i + 1 - 1 = i from rfl]
    calc b ^ i = 1 * b ^ i := this
      _ ≤ x * b ^ i := Nat.mul_le_mul_right _ hx0
      _ ≤ r + x * b ^ i := Nat.le_add_left _ _
  · calc r + x * b ^ i < b ^ i + x * b ^ i := by omega
      _ = (1 + x) * b ^ i := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ b * b ^ i := Nat.mul_le_mul_right _ (by omega)
      _ = b ^ (i + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  · obtain ⟨c, hc⟩ : ∃ c, b ^ i = b * c := ⟨b ^ (i - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩
    rw [hc, Nat.mul_left_comm, Nat.add_mul_mod_self_left, hmod]
  · rw [List.length_cons, List.length_cons, hlen]; omega
  · rw [List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, hnd⟩
    · intro h
      rcases List.mem_cons.mp h with heq | hmem
      · rw [hs₁, hs₂] at heq; exact hxne heq
      · rw [hs₁] at hmem; exact hxu₁ hmem
    · rw [hs₂]; exact hxu₂
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · rw [hs₁]; exact Nat.mod_lt _ hb0
    · rcases List.mem_cons.mp hv' with rfl | hv''
      · rw [hs₂]; exact Nat.mod_lt _ hb0
      · exact hltb v hv''
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact ⟨i, by omega, Or.inl rfl⟩
    · rcases List.mem_cons.mp hv' with rfl | hv''
      · exact ⟨i, by omega, Or.inr rfl⟩
      · obtain ⟨j, hj, hval⟩ := hslot v hv''
        exact ⟨j, by omega, by rw [hlow j hj e₁, hlow j hj e₂]; exact hval⟩

/-- The greedy runs to depth `d`. -/
theorem greedy_reaches {b e₁ e₂ ρ β d : Nat} (hb : 1 < b)
    (hce₁ : Nat.Coprime b e₁) (hce₂ : Nat.Coprime b e₂)
    (hρ : 0 < ρ) (hρb : ρ < b) (hcρ : Nat.Coprime b ρ)
    (hstart : ρ ^ e₁ % b ≠ ρ ^ e₂ % b) (hβ : Nat.Coprime b β)
    (hsep : (e₂ * ρ ^ (e₂ - 1) + β) % b = e₁ * ρ ^ (e₁ - 1) % b)
    (hd : 1 ≤ d) (hcount : 4 * (d - 1) + 2 < b) :
    ∃ r U, GreedyInv b e₁ e₂ ρ d r U := by
  have main : ∀ i, 1 ≤ i → i ≤ d → ∃ r U, GreedyInv b e₁ e₂ ρ i r U := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ hle
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact ⟨ρ, _, greedy_base hb hρ hρb hstart⟩
      · obtain ⟨r, U, hinv⟩ := ih hi (by omega)
        exact greedy_step hb hce₁ hce₂ hcρ hβ hsep hi (by omega) U hinv
  exact main d hd (Nat.le_refl d)

/-! ### §8.6  Theorem F

The `2d` distinct slots are `2d` distinct *digit values*, so at most `b - 2d` of
the `b` values can be missing.  With `d ≈ b/E` that is the `b(1 - 2/E)` of the
report — less than a random candidate's `≈ b/e`, which is the point: this is what
a *constructive* argument can reach, not what is typical. -/

/--
**Theorem F, slot form** — the statement the `2/E` accounting is really about:
some `d`-digit `n` has `2d` *pairwise distinct* values among the low `d` slots of
`n^e₁` and of `n^e₂`.  The deficiency bound below is its corollary.
-/
theorem greedy_distinct_slots {b e₁ e₂ ρ β d : Nat} (hb : 1 < b)
    (hce₁ : Nat.Coprime b e₁) (hce₂ : Nat.Coprime b e₂)
    (hρ : 0 < ρ) (hρb : ρ < b) (hcρ : Nat.Coprime b ρ)
    (hstart : ρ ^ e₁ % b ≠ ρ ^ e₂ % b) (hβ : Nat.Coprime b β)
    (hsep : (e₂ * ρ ^ (e₂ - 1) + β) % b = e₁ * ρ ^ (e₁ - 1) % b)
    (hd : 1 ≤ d) (hcount : 4 * (d - 1) + 2 < b) :
    ∃ n, ∃ U : List Nat, b ^ (d - 1) ≤ n ∧ n < b ^ d ∧ U.length = 2 * d ∧ U.Nodup ∧
      ∀ v ∈ U, ∃ j, j < d ∧ (v = slot b j (n ^ e₁) ∨ v = slot b j (n ^ e₂)) := by
  obtain ⟨r, U, hlo, hhi, hmod, hlen, hnd, hltb, hslot⟩ :=
    greedy_reaches hb hce₁ hce₂ hρ hρb hcρ hstart hβ hsep hd hcount
  exact ⟨r, U, hlo, hhi, hlen, hnd, hslot⟩

/-- How many of the `b` digit values appear nowhere in `n^e₁` or `n^e₂`. -/
def deficiency (b e₁ e₂ n : Nat) : Nat :=
  List.countP (fun v => !memb v (digits b (n ^ e₁) ++ digits b (n ^ e₂))) (List.range b)

/--
**Theorem F.**  Fix a base `b` and exponents `e₁, e₂` with `gcd(e₁e₂, b) = 1`, a
starting digit `ρ` — a unit whose two last digits already differ — and a unit `β`
witnessing that the two progressions have invertible difference
(`e₂ρ^(e₂-1) + β ≡ e₁ρ^(e₁-1)`).  If `4(d-1) + 2 < b`, then some `d`-digit `n`
has combined digit deficiency at most `b - 2d`.

Since `d ≈ b/E` with `E = e₁+e₂`, the counting condition is `4b/E < b`, i.e.
`E ≥ 5` up to the rounding, and the bound is `b(1 - 2/E) + O(1)`.
-/
theorem theorem_F {b e₁ e₂ ρ β d : Nat} (hb : 1 < b) (he₁ : 1 ≤ e₁) (he₂ : 1 ≤ e₂)
    (hce₁ : Nat.Coprime b e₁) (hce₂ : Nat.Coprime b e₂)
    (hρ : 0 < ρ) (hρb : ρ < b) (hcρ : Nat.Coprime b ρ)
    (hstart : ρ ^ e₁ % b ≠ ρ ^ e₂ % b) (hβ : Nat.Coprime b β)
    (hsep : (e₂ * ρ ^ (e₂ - 1) + β) % b = e₁ * ρ ^ (e₁ - 1) % b)
    (hd : 1 ≤ d) (hcount : 4 * (d - 1) + 2 < b) :
    ∃ n, b ^ (d - 1) ≤ n ∧ n < b ^ d ∧ deficiency b e₁ e₂ n + 2 * d ≤ b := by
  obtain ⟨r, U, hlo, hhi, hmod, hlen, hnd, hltb, hslot⟩ :=
    greedy_reaches hb hce₁ hce₂ hρ hρb hcρ hstart hβ hsep hd hcount
  refine ⟨r, hlo, hhi, ?_⟩
  have hb0 : 0 < b := by omega
  have hr1 : 1 ≤ r := Nat.le_trans (Nat.pow_pos hb0) hlo
  -- `r^e` has at least `d` digits, so slots `0 .. d-1` really are digits of it
  have hnum : ∀ e, 1 ≤ e → d ≤ numDigits b (r ^ e) := by
    intro e he
    have : b ^ (d - 1) ≤ r ^ e :=
      Nat.le_trans hlo (by simpa using Nat.pow_le_pow_right hr1 he)
    have := le_numDigits_of_pow_le hb this
    omega
  -- every used value is a digit of `r^e₁` or of `r^e₂`
  have hmem : ∀ v ∈ U, v ∈ digits b (r ^ e₁) ++ digits b (r ^ e₂) := by
    intro v hv
    obtain ⟨j, hj, hval⟩ := hslot v hv
    refine List.mem_append.mpr ?_
    rcases hval with rfl | rfl
    · exact Or.inl (slot_mem_digits hb _ j (by have := hnum e₁ he₁; omega))
    · exact Or.inr (slot_mem_digits hb _ j (by have := hnum e₂ he₂; omega))
  -- so `U` embeds in the digits-that-occur sublist of `range b`
  have hsub : U ⊆ (List.range b).filter
      (fun v => memb v (digits b (r ^ e₁) ++ digits b (r ^ e₂))) := by
    intro v hv
    refine List.mem_filter.mpr ⟨List.mem_range.mpr (hltb v hv), ?_⟩
    exact (memb_iff v _).mpr (hmem v hv)
  have hle : U.length ≤ ((List.range b).filter
      (fun v => memb v (digits b (r ^ e₁) ++ digits b (r ^ e₂)))).length :=
    List.Nodup.length_le_of_subset hnd hsub
  have hcount' := countP_eq_length_filter
    (fun v => memb v (digits b (r ^ e₁) ++ digits b (r ^ e₂))) (List.range b)
  have hsplit := countP_split
    (fun v => memb v (digits b (r ^ e₁) ++ digits b (r ^ e₂))) (List.range b)
  have hlenr : (List.range b).length = b := List.length_range
  show List.countP (fun v => !memb v (digits b (r ^ e₁) ++ digits b (r ^ e₂)))
    (List.range b) + 2 * d ≤ b
  omega

/-! ### §8.7  Non-vacuity

The hypotheses are satisfiable, the conclusion is a real restriction, and the
theorem fires at a pair the report says the counting bound cannot reach. -/

/-- `deficiency` says what it should: 69 in base 10 misses nothing.  (`digits` is
defined by well-founded recursion and does not reduce in the kernel, so the two
digit lists are supplied by §5's evaluations rather than by `decide` alone.) -/
theorem deficiency_sixtynine : deficiency 10 2 3 69 = 0 := by
  show List.countP (fun v => !memb v (digits 10 (69 ^ 2) ++ digits 10 (69 ^ 3)))
    (List.range 10) = 0
  rw [digits_69sq, digits_69cb]
  decide

/-- Theorem F at base 13, `(2,3)`: a 3-digit `n` whose six low slots are distinct. -/
theorem F_base_thirteen :
    ∃ n, 13 ^ 2 ≤ n ∧ n < 13 ^ 3 ∧ deficiency 13 2 3 n + 6 ≤ 13 :=
  theorem_F (b := 13) (e₁ := 2) (e₂ := 3) (ρ := 2) (β := 5) (d := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Theorem F at base 65, `(2,3)`: 26 of the 65 digit values are forced to occur. -/
theorem F_base_sixtyfive :
    ∃ n, 65 ^ 12 ≤ n ∧ n < 65 ^ 13 ∧ deficiency 65 2 3 n + 26 ≤ 65 :=
  theorem_F (b := 65) (e₁ := 2) (e₂ := 3) (ρ := 2) (β := 57) (d := 13)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- And at `(1,3)`, where `E = 4` — the report's §8 says the counting bound fails
for `E = 3, 4`, but `4(d-1) + 2 < b` is sharper than `4b/E < b` and `E = 4` clears
it at every base where the arithmetic side conditions hold. `E = 3` never does. -/
theorem F_base_fortyseven :
    ∃ n, 47 ^ 11 ≤ n ∧ n < 47 ^ 12 ∧ deficiency 47 1 3 n + 24 ≤ 47 :=
  theorem_F (b := 47) (e₁ := 1) (e₂ := 3) (ρ := 2) (β := 36) (d := 12)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The conclusion is a genuine selection, not a property of the range: `169 = 13²`
lies in the very interval `F_base_thirteen` quantifies over, and it fails the
bound.  `169² = 13⁴` and `169³ = 13⁶`, so between them they show two digit values
and miss eleven. -/
theorem digits_169sq : digits 13 (169 ^ 2) = [0, 0, 0, 0, 1] := by
  show digits 13 28561 = [0, 0, 0, 0, 1]
  rw [digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_zero]

theorem digits_169cb : digits 13 (169 ^ 3) = [0, 0, 0, 0, 0, 0, 1] := by
  show digits 13 4826809 = [0, 0, 0, 0, 0, 0, 1]
  rw [digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_zero]

theorem F_conclusion_not_automatic :
    13 ^ 2 ≤ 169 ∧ 169 < 13 ^ 3 ∧ ¬ (deficiency 13 2 3 169 + 6 ≤ 13) := by
  refine ⟨by decide, by decide, ?_⟩
  show ¬ (List.countP (fun v => !memb v (digits 13 (169 ^ 2) ++ digits 13 (169 ^ 3)))
    (List.range 13) + 6 ≤ 13)
  rw [digits_169sq, digits_169cb]
  decide

/-- Odd naturals, as the coprimality hypotheses deliver them. -/
theorem odd_of_coprime_two {x : Nat} (hx : Nat.Coprime 2 x) : x % 2 = 1 := by
  rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with h | h
  · exfalso
    have hd : (2 : Nat) ∣ Nat.gcd 2 x := Nat.dvd_gcd (Nat.dvd_refl 2) (Nat.dvd_of_mod_eq_zero h)
    rw [show Nat.gcd 2 x = 1 from hx] at hd
    exact absurd hd (by decide)
  · exact h

/--
**Where Theorem F stops, and it is a theorem rather than the edge of a scan: no
even base is ever covered.**  If `b` is even then `gcd(e₁e₂, b) = 1` forces both
exponents odd and `gcd(ρ, b) = 1` forces `ρ` odd, so both progression differences
`e·ρ^(e-1)` are odd and their gap is even — no unit `β` can separate them.

This is the honest limitation: the whole `(1,3)` family the repository actually
searches (bases 38, 40, 42, 46) is even, and so is `(2,3)` base 34.  `(2,3)` base
57 is odd but loses the coprimality instead, `3 ∣ 57`.
-/
theorem no_even_base {b e₁ e₂ ρ β : Nat} (hbe : b % 2 = 0)
    (hce₁ : Nat.Coprime b e₁) (hce₂ : Nat.Coprime b e₂) (hcρ : Nat.Coprime b ρ)
    (hβ : Nat.Coprime b β)
    (hsep : (e₂ * ρ ^ (e₂ - 1) + β) % b = e₁ * ρ ^ (e₁ - 1) % b) : False := by
  have hdvd : (2 : Nat) ∣ b := Nat.dvd_of_mod_eq_zero hbe
  have ho : ∀ e : Nat, Nat.Coprime b e → (e * ρ ^ (e - 1)) % 2 = 1 := by
    intro e hce
    have he : e % 2 = 1 := odd_of_coprime_two (hce.coprime_dvd_left hdvd)
    have hr : ρ % 2 = 1 := odd_of_coprime_two (hcρ.coprime_dvd_left hdvd)
    rw [Nat.mul_mod, he, odd_pow hr]
  -- reduce the separation identity mod 2, where both differences are odd
  have h2 : (e₂ * ρ ^ (e₂ - 1) + β) % 2 = e₁ * ρ ^ (e₁ - 1) % 2 := by
    rw [← Nat.mod_mod_of_dvd _ hdvd, hsep, Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.add_mod, ho e₂ hce₂, ho e₁ hce₁] at h2
  have hβodd : β % 2 = 1 := odd_of_coprime_two (hβ.coprime_dvd_left hdvd)
  rw [hβodd] at h2
  exact absurd h2 (by decide)

/-- The two `(2,3)` bases this repository benchmarks, and why each is outside. -/
theorem base_thirtyfour_is_even : 34 % 2 = 0 := by decide

theorem base_fiftyseven_not_coprime : ¬ Nat.Coprime 57 3 := by decide

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
#print axioms Nice.valOf_mod_wsum
#print axioms Nice.valOf_mod_pow_sub_one
#print axioms Nice.pair_mod_pow_sub_one
#print axioms Nice.valOf_mod_pred
#print axioms Nice.valOf_digits
#print axioms Nice.sieve_sound
#print axioms Nice.base_four_gap_core
#print axioms Nice.base_four_sieve_is_incomplete
#print axioms Nice.base_four_sieve_is_incomplete'
#print axioms Nice.base_four_attained
#print axioms Nice.base_four_band_nonempty
#print axioms Nice.residues_nonempty_iff
#print axioms Nice.residues_empty_iff
#print axioms Nice.live_of_residue
#print axioms Nice.no_nice_of_two_adic
#print axioms Nice.two_four_base_seventeen_dead
#print axioms Nice.two_four_base_thirtythree_live
#print axioms Nice.base_ten_residue
#print axioms Nice.residues_empty_of_mod_four_of_C
#print axioms Nice.residues_single_nonempty_iff
#print axioms Nice.single_four_base_twentynine_dead
#print axioms Nice.add_pow_ladder
#print axioms Nice.slot_step
#print axioms Nice.exists_good_digit
#print axioms Nice.greedy_distinct_slots
#print axioms Nice.theorem_F
#print axioms Nice.deficiency_sixtynine
#print axioms Nice.F_base_thirteen
#print axioms Nice.F_base_sixtyfive
#print axioms Nice.F_base_fortyseven
#print axioms Nice.F_conclusion_not_automatic
#print axioms Nice.no_even_base
