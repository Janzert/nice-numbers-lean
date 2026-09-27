# Notes from the formalisation

The working record behind [`NiceNumbers.lean`](NiceNumbers.lean): every result lemma by lemma,
how each theorem is guarded against being vacuous, where formalising changed the mathematics,
what else could be formalised and at what cost, and the traps met along the way. It is written
for someone extending the file. [README.md](README.md) is the place to start.

Theorems are numbered as in the article series
[*Nice Numbers And The Middle Digit Wall*](https://janzert.com/nicenumbers/wall/). The work
itself used letters, in the order it happened (A, B, C, … K); where a date or a cost estimate
below only makes sense in that order, it is kept. The proofs were written against Lean 4.16
and are verified on 4.33.

Several results replaced **exhaustive computer checks** made while the problem was being
explored: for example, a scan of every exponent pair with `e1 ≤ 8`, `e2 ≤ 9` over every base
below 400. A theorem proved for all bases and all pairs is strictly stronger than such a
check, and the tables below say which check each theorem retired.

## Every result, lemma by lemma

| Lean name | statement | earlier evidence |
|---|---|---|
| `no_nice_of_dvd` | **Theorem 1** — `(e1+e2) ∣ e1*(b-1)` ⟹ `numDigits b (n^e1) + numDigits b (n^e2) ≠ b` | a scan over `e1 ≤ 8, e2 ≤ 9, b < 120` |
| `band_nonempty` / `band_nonempty_iff` | **Theorem 1's converse** — above two explicit decidable bounds, a base outside the dead class really does have a candidate; hence Theorem 1 as a biconditional. All bases, all pairs | the same scan, which now needs to cover only the 248 (pair, base) cases below the threshold, all `b ≤ 23` |
| `mul_succ_pow_le` / `double_step_ratio` / `dvd_of_ratio` | **Theorem 1's converse**, its three moving parts — a Bernoulli substitute in ℕ, the squeeze that locks `A1·e2 = A2·e1` at a double step, and the `gcd` step that turns that into the dead-class divisibility | — |
| `two_three_band_nonempty` | **Every base `b ≥ 8` with `b ≢ 1 (mod 5)` has a square/cube candidate** — the classical problem's form of the converse, over all such bases at once | — |
| `base_three_no_candidate` | …and the converse is **false** below the threshold: base 3 is outside the dead class and has no `(2,3)` candidate | none; this is why the theorem carries bounds rather than just the congruence |
| `nice_no_solution` | base `b ≡ 1 (mod 5)` has no square/cube candidate | the `(2,3)` instance of Theorem 1 |
| `one_three_no_solution` | base `b ≡ 1 (mod 4)` has no `(1,3)` candidate | the `(1,3)` instance |
| `two_four_no_solution` | base `b ≡ 1 (mod 3)` has no `(2,4)` candidate | the `gcd > 1` instance |
| `no_nice_of_mod_four` | **Theorem 3** — for **every** pair `e1,e2 ≥ 1`, base `b ≡ 3 (mod 4)` fails the digit-sum identity | — |
| `residues_empty_of_mod_four` | **Theorem 3** as the sieve states it: `R_b = ∅` for `b ≡ 3 (mod 4)`, every pair | a scan over `e1 ≤ 8, e2 ≤ 9, b < 400` |
| `base_unique` / `bands_disjoint` | **The band's shape** — the length identity holds for at most one base, so distinct bases' bands are disjoint | a scan over five pairs, `b < 500`, ~2 700 values of `n` |
| `numDigits_mono` / `band_lengths_const` / `band_convex` | **The band's shape**, within one base — both lengths are constant across the band, and anything between two band members is one | none; see below |
| `no_nice_of_universal_clash` | **Theorem 2**, operative half — a base where `x^e1 ≡ x^e2 (mod b)` for every `x` has no pandigital `n` | — |
| `clash_iff_dvd_clashMod` | **Theorem 2**, classification — the clashing bases are exactly the divisors of `N(e1,e2)`, computed as a finite gcd | a scan over `b < 200`, `e1 ≤ 5, e2 ≤ 7` |
| `clash_prime_pow_iff` / `prime_pow_dvd_clashMod_iff` | **Theorem 2**, local criterion — `p^a ∣ N` iff `a ≤ e1` and every unit mod `p` has order dividing `e2-e1` | — |
| `valOf_mod_wsum` / `valOf_mod_pow_sub_one` | **Theorem 5**, the engine — mod `b^j - 1` a digit list is worth `Σ_t b^t S_t`, the totals of its positions `≡ t (mod j)`. All `b`, all `j`, all lists | a sample of 200 000 random shuffles at `j = 2, 3` |
| `valOf_mod_pred` / `sieve_sound` | **Theorem 5**, soundness — casting out `b-1`s, hence `I(m) ⊆ {z ≡ T mod gcd(m,b-1)}` for every modulus | — |
| `base_four_sieve_is_incomplete` | **The naive completeness claim is false** — base 4, lengths `(2,2)`: no pandigital pair has `x+y ≡ 2 (mod 5)`, though `gcd(5,3) = 1` means the digit sum permits it | none; this one *refutes* a claim the informal write-up used to make |
| `sieve_complete` | **Theorem 5** — where the class sizes admit a legal `p` with the no-gap conditions, and are big enough, **every** residue the digit-sum congruence permits is the sum of a genuine pandigital pair of those digit lengths, leading digits included. All bases, all `j`, all lengths, all `p` | a check of four `(b, L1, L2, j)` rows by dynamic programming — a *weaker* statement, since that ignored the leading-digit rule |
| `blocks_hit` | **Theorem 5**, block level — the same conclusion about `Σ_t b^t S_t`, with no digit lengths and no leading digits in the statement | — |
| `pick_sum` | **Theorem 5**, engine 1 — the `p`-element sublists of a run of `p+q` consecutive integers realise every sum in `[min, min + pq]`, with no gaps | — |
| `cover_exists` | **Theorem 5**, engine 2 — mixed-radix covering: if each place `b^t` opens before the lower places run out, `{Σ ν_t b^t : ν_t ≤ N_t}` is a full interval | — |
| `blk_identity` | **Theorem 5**, the join — an identity in `ℕ`, not a congruence: `X + (b-1)·Σ_t b^t σ_t + (b^j-1)·τ_{j-1} = Σ_t b^{t+1}·ΣA_t` | — |
| `residues_nonempty_iff` / `residues_empty_iff` | **Theorem 4** — `R_b = ∅` iff `a = 1`, or (`a ≥ 3` and `e2-e1` even and `e1 ∤ a-1`), where `a = v_2(b-1)`. All bases, all pairs | none |
| `residues_single_nonempty_iff` | **Theorem 4**, single exponent — `R_b ≠ ∅` iff `a = 0` or `e ∣ a-1` | a list of bases taken from a scan |
| `no_nice_of_two_adic` | **Theorem 4**, operative form — a base in a dead 2-adic class admits no `n` satisfying the digit-sum identity | — |
| `residues_empty_of_mod_four_via_two_adic` | **Theorem 3 is the `a = 1` case of Theorem 4**: `b ≡ 3 (mod 4)` is exactly `v_2(b-1) = 1`. Not a replacement — Theorem 4 assumes `e1 < e2` and Theorem 3 does not, so the degenerate `e1 = e2` stays Theorem 3's alone | — |
| `add_pow_ladder` / `slot_step` | **Theorem 7**, the engine — `(r + x·b^i)^e ≡ r^e + e·r^{e-1}·x·b^i (mod b^{i+1})` for `i ≥ 1`, and hence that adding digit `x` at level `i` moves slot `i` of `n^e` along an arithmetic progression with difference `e·r^{e-1} (mod b)`. This is the recurrence the search's GPU kernels advance the digit with, and the "two slots per digit" law itself | the claim was used in the search code and stated in its comments, never proved |
| `exists_good_digit` | **Theorem 7**, the pigeonhole — two maps injective on `{0,…,b-1}` colliding at most once leave a nonzero digit avoiding a list `U` in both, once `2\|U\| + 2 < b` | — |
| `greedy_distinct_slots` | **Theorem 7**, slot form — some `d`-digit `n` has `2d` pairwise-distinct values among the low `d` slots of `n^{e1}` and `n^{e2}` | — |
| `greedy_deficiency_le` | **Theorem 7** — hence combined digit deficiency `≤ b - 2d`, i.e. `b(1 - 2/E)` since `d ≈ b/E` | none; see below |
| `no_even_base` | **Theorem 7**, its limit — an even base admits no `β`, so Theorem 7 covers only odd bases | a scan that had found only the boundary |
| `pandigital_length` / `pandigital_digitSum` | **Theorem 6**, the bridge — pandigitality *implies* the two numerical consequences §1–§3 take as hypotheses, so Theorem 6 is a statement about nice numbers and not about numbers assumed to behave like them | the file had asserted the implication only at 69 |
| `pandigital_pow_bounds` | **Theorem 6**, the band without roots — `b^(b-2) ≤ n^E < b^b` for every pandigital `n`, by multiplying the two per-exponent length bounds. No jump structure, no `gcd`, no exponents in the statement | — |
| `adm_of_pandigital` | **Theorem 6** — every pandigital `n` is in that band and passes `adm`, a test reading only `n mod (b-1)` and `n mod b^k`. All bases, all pairs, all `k`, all `n` | none |
| `countP_run_le` / `adm_period` | **Theorem 6**, the closed form — `adm` has period `(b-1)·b^k`, and a periodic test on a segment is counted by one window times `⌈len/W⌉` | — |
| `countP_pandigital_le_adm` / `countP_pandigital_le_window` | **Theorem 6**, counting and closed forms — `#{nice in band} ≤ countP adm (band) ≤ countP adm (one window) · ⌈len/W⌉` | — |
| `occ_low_top_le` | **Theorem 6**, condition 4's engine — the low `k` and top `h` slots are disjoint stretches of the digit list, so their occurrence counts add inside it. Needs `k + h ≤ L`, and that is the only place the cap is used | — |
| `admTop_of_pandigital` / `countP_pandigital_le_admTop` | **Theorem 6, condition 4** — on an interval where the two lengths are constant, every pandigital `n` passes all four filters, and at most `countP admTop` of the interval is nice. All bases, all pairs, all `k`, all `h` | the bound's evaluation in code, which is still checked separately: see "Proved is not the same as evaluated" |
| `topSlots_const` / `no_pandigital_of_top_clash` | **Theorem 6**, the interval form — where the top quotient agrees at an interval's two ends it is constant throughout, so an interval whose top digits already clash holds no nice number. `base_seventeen_dead_interval` retires 95 consecutive candidates from four divisions | none; this is what makes condition 4 a decomposition rather than a per-candidate test |
| `base_ten_nice_iff` | **The set of `(2,3)`-nice numbers in base 10 is exactly `{69}`** — the sharpness witness for Theorem 6, and the only equality case known | a 53-number scan, never a theorem |
| `base_ten_exact_band` / `sixtynine_unique_top` | The same uniqueness a second, independent way — the *exact* band `[47,100)` (which the length identity gets from §9.4's crude one) and all four conditions at depth `(k,h) = (2,2)`, where §9.8 needed `(4,0)` | — |
| `pow_self_le_fact` | **Theorem 9**, the analytic input — `b^b ≤ 4^b·b!`, from `b!·b^b ≤ (2b)! ≤ 4^b·(b!)^2`. Two inductions, no Stirling, no reals | — |
| `band_of_interval` | **Theorem 9**, the band — if `E ∣ b-2` and `2^e_i ≤ b`, all `b^q` integers in `[b^q, 2b^q)` are candidates, `q = (b-2)/E`. Exhibited, not estimated: no root extraction and no jump structure | every earlier band lower bound was a computation |
| `model_diverges` | **Theorem 9** — for every pair and every `M`, arbitrarily large even bases with `E ∣ b-2` and `\|band\|·b!/b^b > M`. The heuristic diverges, unconditionally | — |
| `resOK_zero_of_even` / `no_clash_of_large` | **Theorem 9**, liveness — `ρ = 0` is a residue at every even base (Theorem 4's `v_2(b-1)=0` case), and no base above `N(e1,e2)` clashes. With the band exhibited, that is all four proved obstructions missing the family | — |
| `nice_base_unique` | **Theorem 8** — a nice number is nice in exactly one base: the band's shape at the level of solutions rather than candidates | — |
| `infinitude_iff` | **Theorem 8** — infinitely many nice numbers **iff** infinitely many bases host one, for every pair. Both directions from `pandigital_pow_bounds` | asserted in prose ("the same axis"), never proved |
| `ModelPositive` / `conditional_infinitude` | **Theorem 10** — the single hypothesis that closes the gap, and the implication. Nothing here proves the hypothesis | — |
| `divergence_is_not_existence` | **The guard** — `(2,3)`, `b = 20s+7`: exhibited band, heuristic past any `M`, and **no** nice number, by Theorem 3. So `ModelPositive` cannot drop its arithmetic clauses | none; this one *refutes* the weakening a reader would reach for |

**`residues_empty_of_mod_four` exists because a check was deleted.** The scan it replaced did
not check the digit-sum identity that `no_nice_of_mod_four` refutes — it checked that the
*residue set* `R_b = {ρ : ρ^e1+ρ^e2 ≡ T (mod b-1)}` is empty, which is the form a sieve
actually uses and which the digit-sum theorem does not literally imply (it assumes a
solution's digit sums, not a bare congruence class). Same two-line parity argument, stated
over the congruence instead. **When deleting a finite check in favour of a proof, compare the
two statements, not the two section headings** — the check is usually of some *proxy* for the
theorem, and the proxy is what the rest of the code depends on.

`numDigits` and `digitSum` are defined from scratch by repeated division (60 lines, including
`bounds_of_numDigits`: `numDigits b x = k+1 ↔ b^k ≤ x < b^(k+1)`, and `digitSum_mod`: casting
out `b-1`s). Nothing about digits is assumed. §5 adds `digits` (the digit *list*) and
`Pandigital` — the first time the file states the solution condition itself rather than one
of its two numerical consequences, because a digit *collision* is invisible to both of them.

**The band's shape was proved late (2026-09-22)**: `numDigits_mono` (more `n`, never fewer
digits), then `band_lengths_const` and `band_convex`. The article had already called it
machine-checked, and used "an interval where the two lengths hold steady, which is what a
band is" to apply Theorem 6's fourth condition to a whole band, before any of it existed —
only disjointness (`bands_disjoint`) did. Each is `numDigits_antitone`'s argument in the other
variable, and `omega` closes both band lemmas from four monotonicity facts. The lesson: an
appendix saying "machine-checked" is written by the same hand as the claim, so it cannot be
the check. Search the file for the statement.

## Non-vacuity — the check that matters most

An impossibility theorem with contradictory hypotheses proves itself. §4 of the file rules
that out, kernel-checked:

* `length_identity_holds : numDigits 10 (69^2) + numDigits 10 (69^3) = 10`
* `digitsum_identity_holds : 2 * (digitSum 10 (69^2) + digitSum 10 (69^3)) = 10 * (10-1)`

i.e. 69 in base 10 — the only known nice number — satisfies both hypothesis families. Then
two theorems shown *firing*: `base_eleven_dead` (Theorem 1 at `b = 11`) and `base_seven_dead`
(Theorem 3 at `b = 7`, where Theorem 1 says nothing because `7 ≢ 1 mod 5`), plus
`base_seven_dead'` at exponents `(3,8)` to show Theorem 3 really is pair-independent.

**The band's shape** needs the same guard for the opposite reason — "at most one base" is
trivially true of an `n` that has none. `sixtynine_in_band : InBand 10 2 3 69` supplies the
witness, and `sixtynine_only_base_ten` then reads off that base 10 is the *only* base 69 is a
candidate in, over all bases at once and with no finite search.

**Theorem 6 needs the guard in a third shape again: an upper bound is vacuous when it is not
attained, and useless when the thing it bounds is empty.** Both are answered at once by
`base_ten_nice_iff` — the bound is 1, the truth is 1, and 69 is the witness. The second
witness, `base_seventeen_bound` (`≤ 585` from a 272-number window over a band of 10 347), is
there because base 10 is the wrong shape to exercise the closed form at all: `W = 90 000`
against a band of 60.

**Condition 4 needed a third witness of its own, for a reason neither of those two has**: it
is the only filter here whose value can be *shared* by a whole run of candidates, so the
thing to witness is not one `n` but one interval. `base_seventeen_dead_interval` retires
`[4913, 5008)` — 95 consecutive candidates — from the observation that the top two digits of
`n^2` and of `n^3` both read `(0,1)` there. The honest comparison is with what the congruence
filters do to the same 95: five alive at `k = 1`, three at `k = 2`, one at `k = 3` and
`k = 4`, and zero only at `k = 5`, which is 1 419 857 tabulated residues and a test per
candidate, against two divisions for the run.

**Theorems 8–10 need the guard in a fourth shape: a conditional theorem is worthless if its
hypothesis is unsatisfiable, and *dangerous* if the hypothesis is stronger than the reader
thinks.** Both ends are covered. `base_eight_nice` puts a real solution in the divergence
family — base 8 is even, `3 ∣ 8-2`, and `174 = 256_8` is `(1,2)`-nice there — so
`ModelPositive`'s shape is satisfiable; and `divergence_is_not_existence` proves that the same
family, with the parity clause dropped, contains infinitely many **provably empty** bases
with the same divergent heuristic. Writing the first witness is what forced the second: base
8's `b^q·b!/b^b` is 0.15, so the family demonstrably contains bases where the heuristic and
the truth disagree in one direction, and the question of the other direction answers itself.

**Which filter each witness actually covers is not obvious and had to be measured.** At base
10 with `k = 4` the low slots alone already pin 69, so `base_ten_survivors` survives deleting
`resOK` from `adm` — it is `base_seventeen_window` that catches that deletion. Three other
mutations (depth `k = 3` instead of `4`, deleting `lowOK`, widening the band by moving `lo`
from 39 to 30) are each rejected by the base-10 witness. A witness that passes under a
deleted hypothesis is not a witness for that hypothesis, and only running the mutation says
which is which.

**Condition 4's base-10 witness is the better one on exactly that axis, and it was free.**
`base_ten_top_survivors` reaches the same `{69}` at `(k,h) = (2,2)`, and there **all three
filters bite**: deleting the residue filter leaves `{59, 69}`, deleting the top half leaves 9
survivors, deleting the low half leaves 14, and shortening either depth by one leaves 2 or 5.
Eight mutations are rejected in all — those five, plus starting the interval at the crude
band's 40 instead of the exact band's 47, reading base 17's interval one past its end, and
naming a digit there that does not clash. **The lesson from the pair is about depth, not
about the mutations**: the deeper single-ended witness is the weaker one, because at `k = 4`
the low filter has enough slots to do the whole job by itself and the others are never
asked. Witness at the *shallowest* depth that still attains the bound.

Theorem 2 needs the guard twice over, because it introduces a *definition*:

* `sixtynine_pandigital : Pandigital 10 2 3 69` — the definition is satisfiable, so
  `no_nice_of_universal_clash` is not refuting the empty set. (`digits 10 4761 = [1,6,7,4]`,
  `digits 10 328509 = [9,0,5,8,2,3]`, ten values, each once.)
* `base_ten_no_clash : ¬ UniversalClash 10 2 3` — and Theorem 2 had better *not* kill base
  10, or it would contradict 69. `N(2,3) = 2` and `10 ∤ 2`.

Then two theorems shown firing where Theorems 1 and 3 say nothing at all:
`one_three_base_six_dead` (base 6 is `2 mod 4`, so Theorem 1 misses it, and even, so Theorem
3 misses it — but `x ≡ x^3 mod 6` always) and `two_four_base_twelve_dead`. Plus
`clash_three_one_three` and `nine_no_clash_one_three`, which run the local criterion forwards
and backwards on numerals.

**Theorem 4's guard is the sharpest of the lot, because it is a biconditional: both
directions have to be shown firing, or the theorem could be the constant `False` or the
constant `True`.**

* `two_four_base_seventeen_dead` — `(2,4)` at base 17, where **Theorems 1, 2 and 3 all say
  nothing** (`17 % 3 = 2`, `17 % 4 = 1`, `17 ∤ N(2,4) = 12`) and Theorem 4 kills it alone.
* `two_four_base_thirtythree_live` — base 33, one step up in `v_2(b-1)`, is *not* killed,
  and the witness `ρ = 4` the theorem names is checked by `decide`. So the `e1 ∣ a-1`
  boundary is sharp, not slack.
* `base_ten_live` / `base_ten_residue` — base 10 had better be alive, or Theorem 4 would
  contradict 69; and 69 itself is exhibited as a residue.
* `single_four_base_twentynine_dead` / `single_four_base_thirtythree_live` — the same pair of
  ends for the single-exponent form.

Six statement-level mutations were checked and all six are rejected: declaring base 33 dead
the way base 17 is, weakening `a ≥ 3` to `a ≥ 2`, dropping the `e2-e1` odd clause, widening
`a ≤ 2` to `a ≤ 3`, moving the odd-gap witness from `(b-1)/2 - 1` to `(b-1)/2 + 1`, and
(single exponent) `e ∣ a` for `e ∣ a-1`.

**Theorem 5 needs the same kind of guard as Theorem 4, and it caught a real bug.** Its
hypothesis is a conjunction of no-gap inequalities, and the first version stated them for
*every* `t` rather than `t < j`. That type-checks and it is **unsatisfiable** — `b^t` outruns
any fixed `Σ_{s<j} N_s b^s` — so the theorem was vacuous while looking correct. Nothing but a
witness finds that.

* `base_ten_j_two_complete` — base 10, `j = 2`, digit lengths `(4,6)`: the lengths of
  `69^2 = 4761` and `69^3 = 328509`. `c = (5,5)`, `p = (5,0)`, `N = (25,0)`, and the
  conclusion is that every residue mod `99` allowed by casting out 9s is the sum of a genuine
  pandigital `(4,6)` pair. All the hypotheses discharge by `decide`.
* `base_ten_j_five_rider_fails` — and at `j = 5`, which is exactly where base 10's sieve
  *does* gain (`11111 = 41·271` has order 5 and misses two residues), the class sizes are
  `(3,2,2,2,1)` and the `c_t ≥ 2` half of the rider fails. The theorem stops precisely where
  the counterexample starts.
* `base_four_rider_fails` / `base_four_clears_the_other_half` /
  `base_four_clears_the_no_gap` — base 4, lengths `(2,2)`, is the sharper test: it clears
  `c_t ≥ 2` **and** the no-gap conditions (`p = (2,0)` gives `N = (4,0)`, `b^1 = 4 ≤ 5`,
  `K-1 = 4`), both by `decide`, and is stopped only by `c_t ≥ 3` at the class carrying the
  second number's leading slot. Checking what it *passes* is the point: a witness that fails
  several hypotheses at once says which one is load-bearing only if the others are shown to
  hold. Without that clause the theorem would contradict `base_four_sieve_is_incomplete`,
  three sections earlier in the same file. **Both halves of the rider are load-bearing, and
  each is pinned by a witness that fails on it alone.**

**Theorem 7 needs a guard the impossibility theorems do not, because it is constructive.** An
impossibility theorem is worthless if its hypotheses are contradictory; a *construction* is
worthless if its conclusion is free. Both are checked:

* `greedy_deficiency_thirteen`, `greedy_deficiency_sixtyfive`, `greedy_deficiency_fortyseven` — the hypotheses are
  satisfiable, at `(2,3)` bases 13 and 65 and at `(1,3)` base 47, each with the `ρ` and `β`
  the theorem asks for supplied as numerals and every side condition closed by `decide`.
  Base 65 forces 26 of its 65 digit values to occur.
* `greedy_deficiency_not_automatic` — `169 = 13^2` lies inside the very interval
  `greedy_deficiency_thirteen` quantifies over and **fails** the bound: `169^2 = 13^4` and
  `169^3 = 13^6`, so between them they show two digit values and miss eleven. The conclusion
  is a selection, not a property of the range.
* `deficiency_sixtynine : deficiency 10 2 3 69 = 0` — the definition means what it says,
  checked against the one number known to miss nothing.
* `no_even_base`, `base_thirtyfour_is_even`, `base_fiftyseven_not_coprime` — the two `(2,3)`
  bases most often used as search benchmarks are **outside** the theorem, and the file says
  so rather than leaving it to be discovered. The first of those is a theorem about every
  even base, not a remark about 34.

Fourteen mutations were checked and all fourteen are rejected. The four that matter:
weakening any of the three counting budgets (`4(d-1)+2 < b` in the theorem, `4i+2 < b` in the
step, `2|U|+2 < b` in the pigeonhole) from `<` to `≤`; dropping the leading-digit guard from
the bad set; dropping the collision term from the bad set; and dropping the factor `e` from
the ladder's slope. Also rejected: each of `hstart`, `hβ`, `hce1`, `hcρ` replaced by a
triviality, the conclusion strengthened to `2d+1`, a perturbed `β` in a witness, and a
witness pushed one level past its counting bound.

## The formalisation improved the mathematics

The informal proof of Theorem 1 goes through `f(t) = ⌊e1t⌋ + ⌊e2t⌋`, its jump points `j/e1`
and `i/e2`, which of them coincide, and a `gcd` bookkeeping step. None of that survives
contact with Lean, and it turns out none of it is needed. The Lean proof is:

1. `b^a ≤ n^e1` and `n^e2 < b^(c+1)` both bound the same quantity `n^(e1e2)`, giving
   `a·e2 < (c+1)·e1`. Run it the other way for `c·e1 < (a+1)·e2`. Those two confine `(a,c)`
   to a window of width exactly `e1+e2`.
2. The length identity turns the window into `E·k < E·(a+1) < E·(k+1)` where `E = e1+e2` and
   `k` is the cofactor from the divisibility hypothesis, which forces `k < a+1 < k+1`.

No floors, no reals, no `gcd`, no case analysis — and the hypothesis is the single
divisibility `(e1+e2) ∣ e1*(b-1)`, which is *sharper to state* than
`b ≡ 1 mod (e1+e2)/gcd(e1,e2)` and equivalent to it.

**Band disjointness went the same way, and further.** The informal write-up called it "a
routine exercise from the exact endpoints `b^{j/e1}`, `b^{i/e2}`", and the estimate said "same
window technique as Theorem 1, ~1 day". Neither the endpoints nor the window are needed, and
it took an afternoon. `numDigits b x` is *antitone in `b`* (`b^k ≤ b'^k`, so a length bound
in the larger base is one in the smaller), hence `numDigits b x + numDigits b y − b` is
**strictly decreasing in `b`** and vanishes at most once. That is the whole proof — three
short lemmas, `omega` closing each branch of a trichotomy.

Two consequences of proving it that way. It never mentions `e1`, `e2` or `n`, so the theorem
is about *any two values* `x, y`: `base_unique` covers every exponent pair, including ones
nobody has tabulated, and `InBand`/`bands_disjoint` are the `(e1,e2)` corollary rather than
the content. And it is strictly stronger than the crude interval argument, which only ever
gave `≤ 2` bases. **The lesson repeats Theorem 1's: the informal proof reached for the sharp
endpoints because they were already derived and sitting there, and the sharp endpoints were
the reason it looked like a day's work.**

**Theorem 4 was priced at "Hensel plus the structure of `(ℤ/p^k)*`", and needed neither —
nor the CRT, nor a single odd prime.** The estimate came from the informal framing: `R_b = ∅`
iff the congruence is unsolvable modulo some `p^a ‖ b-1`, so decide it prime power by prime
power. That framing is true and it is the expensive way round. Three things collapse it:

1. **Odd prime powers never obstruct, because `ρ = 0` solves them.** `2T = b(b-1)` makes
   `T ≡ 0` modulo the odd part of `b-1`, so the local congruence there is
   `ρ^{e1} + ρ^{e2} ≡ 0`. Everything is 2-adic, which had been *observed* empirically ("all
   2-adic") without anyone noticing it was forced.
2. **At 2 the question is a valuation count, not a solvability question.**
   `T ≡ 2^{a-1} (mod 2^a)`, and `S ≡ 2^{a-1} (mod 2^a)` iff `v_2(S) = a-1` *exactly*. So one
   only has to ask which valuations `ρ^{e1}(1 + ρ^{e2-e1})` can have — three cases, three
   clauses, no group structure anywhere.
3. **Writing the witnesses down removes the CRT.** The half that looks like it needs assembly
   ("solvable locally everywhere ⟹ solvable") is discharged by four explicit residues. The
   `e2-e1` odd witness is the one that makes this work: `(b-1)/2 - 1` is `-1` mod the odd
   part, not `0`, and the opposite exponent parities cancel the sign. Insisting on a witness
   that is `0` there is what forces an inverse, and an inverse is what forces CRT.

**The lesson is the same one Theorems 1 and 2 and band disjointness taught, and this is its
fourth outing: the informal proof reached for the machinery that would decide the *general*
local question, when the specific local question had a one-line answer.** Every estimate in
the cost table below that was written from an informal proof sketch has so far been too
pessimistic, and always for this reason.

**Theorem 2 was priced at a week "because it needs Carmichael `λ`", and `λ` turned out to be
in the *statement*, not in the proof.** The estimate said the sufficiency half was the only
cheap piece. In fact all of it went through in an afternoon, core-only, once three things
were noticed:

1. **`λ(p^a) ∣ d` is an evaluation, not a hypothesis.** What the argument actually uses is
   "every unit mod `p` has order dividing `d`". State the criterion that way
   (`clash_prime_pow_iff`) and the Carmichael function disappears from the theorem entirely;
   it reappears only if you want to *compute* the answer.
2. **The global statement needs no CRT and no factorisation.** `b` clashes iff
   `b ∣ x^{e2} - x^{e1}` for every `x`, so the clashing bases are the divisors of
   `G = gcd_x (x^{e2} - x^{e1})` by definition — divisor-closure, lcm-closure and boundedness
   all at once. The `x = 2` term bounds every clashing base by `2^{e2} - 2^{e1}`, which also
   truncates the gcd to a finite one, so `N` becomes a *computation the kernel can do*
   (`clashMod 3 7 = 120` by `decide`, no axioms at all). The informal proof assembles the
   local criteria by CRT; it never needs to.
3. **Sufficiency needs the dichotomy `p ∣ x` or not, not the splitting `x = p^v u`.** If
   `p ∣ x` then `p^a ∣ p^{e1} ∣ x^{e1}` and both powers vanish; otherwise `x` is a unit. The
   valuation `v` is never used.

The gcd form is also the better *definition* outside Lean: the exploratory code that computed
`N` iterated a hardcoded prime list `[2..47]`, which is silently wrong once `e2 - e1 ≥ 47`,
while the gcd form has no such parameter.

**Theorem 7 was priced at "~2 weeks, the bookkeeping is not small", and cost an afternoon —
but for the opposite reason to Theorems 1, 2 and 4.** Those were overpriced because the
informal proof reached for machinery it did not need. Theorem 7 was overpriced because the
informal *statement* was not yet a theorem, and once it was made into one the proof was
short. Three things came out of making it precise, and two of them correct the informal
account:

1. **The side condition is a hypothesis about one number, not an `O(db)` check.** The
   informal account says at most `2·|Used|` digits are killed "plus the `x` for which the two
   new digits coincide" — *the* `x`, singular, which is true only when `α_{e1} - α_{e2}` is a
   unit mod `b`, and it flags this as a side condition "which is `O(db)`". But
   `α_e = e·r^{e-1} (mod b)` depends on `r` only through `r mod b`, and `r mod b` is the
   **starting digit `ρ`, fixed at level 0 and never touched again**. So the condition is one
   check per candidate `ρ`, `O(b)` in total, not one per level. In Lean it becomes a unit `β`
   with `e2ρ^{e2-1} + β ≡ e1ρ^{e1-1}`, carried as a hypothesis and discharged by `decide` at
   each witness base.
2. **The counting bound is `E ≥ 4`, not `E ≥ 5`.** The informal account gets `4b/E < b` by
   rounding `d ≈ b/E` and concludes the bound "fails for `E = 3, 4`". The exact condition is
   `4(d-1) + 2 < b`; at `E = 4` that is `≈ b - 2 < b` and it **holds**. `(1,3)` clears it at
   bases 7, 11, 19, 23, 31, 35, 43, 47, 55, 59 and 67 — `greedy_deficiency_fortyseven` is base 47 — and
   misses at base 46 by exactly zero (`4·11 + 2 = 46`). `E = 3` never clears it. So the honest
   statement is that `E = 4` is marginal and base-dependent, not dead.
3. **`gcd(e1e2, b) = 1` is where the theorem actually stops, and it is worse than it looks:
   no even base is ever covered.** That is `no_even_base`, proved rather than observed — an
   even `b` forces both exponents and `ρ` odd, hence both `α_e = e·ρ^{e-1}` odd, hence an even
   gap, hence no unit `β`. Every `(1,3)` base that can hold a solution is even, so that whole
   family is out, and so is `(2,3)` base 34; `(2,3)` base 57 is odd but loses the coprimality instead. Over all
   ten pairs with `e2 ≤ 5` and bases `< 70` the theorem fires at 174 (pair, base) instances,
   **every one at an odd base**. That is why Theorem 7 retired no exhaustive check: those
   checks are the *only* evidence for the cases the theorem cannot reach. Scanning found the
   boundary; proving it is what turned "34 and 57 happen to be out" into "every even base is
   out, necessarily".

## Why not Mathlib

The offer was taken seriously and declined on measurement, not principle. What Mathlib would
have supplied is `Finset` counting; what the proof actually needs is six list lemmas
(`countP` subadditivity, `countP ≤ 1` under a uniqueness hypothesis, `countP` of a membership
test bounded by the list's length, `countP p + countP ¬p = length`, `countP > 0 → ∃`, and
`countP = (filter).length`) totalling about 60 lines — and the one lemma that would have been
genuinely painful to redo, `List.Nodup.length_le_of_subset`, is **already in core**. Against
that: a lakefile, a multi-gigabyte pinned dependency, and a compile going from seconds to
minutes, for a file whose stated value is having nothing that can rot. Two core gaps are
worth knowing about if this is revisited: **`by_contra` and `set` are Mathlib tactics**
(`rcases`, `obtain` and `rintro` are core), and there is no `ring` — the ladder's polynomial
identity is closed by `simp` with the associativity/commutativity lemmas after generalising
`r^{e-1}` out.

The cost is §0's 60 lines of digit definitions and the occasional missing lemma —
`pow_lt_pow_left'` is one — which is a good trade for a file this size.

## Traps

**`digits` does not reduce in the kernel.** It is defined by well-founded recursion, so
`decide` cannot evaluate anything built on it. `deficiency_sixtynine` and
`greedy_deficiency_not_automatic` therefore route through explicit `digits_step` chains, exactly
as §5's `digits_69sq` already did. The error is legible (`reduction got stuck at the
Decidable instance`), but it appears only at the `decide`, a long way from the definition
that caused it. The same applies to `numDigits`, which is why Theorem 6's `topSlots` takes the
length `L` as a parameter instead of computing it.

**`omega` does not know that a power is nonnegative.** It abstracts `2^e1`,
`4^(2*(e1+e2))` and friends as opaque atoms — correctly — but does not add the `≥ 0` that
every ℕ atom satisfies, so a goal that follows in one line from `t ≤ h` fails, and fails with
a printed "possible counterexample" whose constraint list is satisfiable only because those
atoms are allowed to be negative. Three `Nat.one_le_pow` hypotheses in the context fix it.
This is not the core-vs-Mathlib class of problem; it is a real gap in `omega`'s
preprocessing, and the symptom reads like "your goal is false" rather than "I am missing a
fact". Any statement whose hypotheses are built out of `2^e` will hit it.

## What else is formalisable, and what it would cost

| result | verdict | notes |
|---|---|---|
| ~~**Band disjointness**~~ | **done** (`base_unique`, `bands_disjoint`) | Estimated at ~1 day by the window technique; cost an afternoon by antitonicity of `numDigits` in the base, and came out pair-independent. See above. |
| ~~**Theorem 4**~~ — classification of `R_b = ∅` | **done** (`residues_nonempty_iff`, `residues_empty_iff`, `residues_single_nonempty_iff`) | Costed as "easy per pair, hard in general — needs Hensel plus the structure of `(ℤ/p^k)*`, Mathlib-scale, ~1 week per family". Wrong on every count: it is a closed form in `v_2(b-1)`, no odd prime enters, and it cost an afternoon core-only. See above. |
| ~~**Theorem 2**~~ — `q_1(b)=0 ⟺ b ∣ N(e1,e2)` | **done** (`no_nice_of_universal_clash`, `clash_iff_dvd_clashMod`, `clash_prime_pow_iff`) | Estimated at ~1 week, "needs Carmichael `λ`"; cost an afternoon once `λ` was pushed out of the statement. See above. **What is left is one classical evaluation**: `exponent((ℤ/p^aℤ)*) = λ(p^a)`, i.e. the structure theorem for that group. Mathlib has `Monoid.exponent`; the value at `p^a` would still have to be proved, and only the *closed form* for `N` depends on it. This is now the only place in the file where core's lack of a library is the binding constraint. |
| ~~**Theorem 7**~~ — the `2/E` greedy bound | **done** (`greedy_distinct_slots`, `greedy_deficiency_le`) | Estimated at "medium-hard, ~2 weeks" for the digit ladder plus a greedy pigeonhole induction; cost an afternoon, and the ladder and the pigeonhole were both short. What the estimate missed is that the *statement* needed two repairs first — the side condition is `O(b)` not `O(db)`, and the counting bound reaches `E = 4`. See above. |
| ~~**Theorem 5**, soundness~~ — the sieve never sees more than `Σ_t b^t S_t` | **done** (`valOf_mod_wsum`, `sieve_sound`) | Estimated inside a "~1 month" for the whole proposition; the soundness half cost an hour, because it is an induction on a list and needs no combinatorics at all. |
| ~~**Unconditional completeness**~~ — no modulus adds density | **done: it is FALSE** (`base_four_sieve_is_incomplete`) | 256-case kernel `decide` on base 4, lengths `(2,2)`. Both natural mutations of the check are rejected, and `base_four_attained` supplies the three witnesses, so it is neither vacuous nor slack. |
| ~~**Theorem 5**, the conditional theorem~~ | **done** (`sieve_complete`) | Costed as "hard, ~1 month", on the grounds that it needs the arena as an *explicit permutation* of `{0,…,b-1}` and core has no `Finset`/`Multiset`. It cost a day. The premise was right and the conclusion wrong: **the absence of `Finset` is what made it cheap, not expensive.** `occ v : List Nat → Nat` is additive over `++`, so "is a permutation" is `∀ v, occ v l = 1` and every step of the construction is an arithmetic identity about counts — no `Perm`, no quotient, no `Multiset.map` congruence lemmas. Reaching for the set-theoretic vocabulary is what would have cost a month. |
| **The sharp form of Theorem 5** — `c_t ≥ 2` suffices | **not yet a proof at all** | Open on paper first. Formalising is not the bottleneck — though formalising Theorem 5 did shorten the distance: the rider it actually needs is `c_t ≥ 2` everywhere plus `c_t ≥ 3` at one named class, so the sharp form is one class away rather than `j`. |
| **Theorem 5**, descent to a general modulus | **an afternoon, low value** | The theorem is proved at `b^j - 1`; getting `I(m) = {z ≡ T mod gcd(m,b-1)}` for every `m` of order `j` is one CRT step. Core has no CRT, so it is a real if small job, and it changes nothing operational. |
| **Theorem 5**, the `j = 2` converse | **an afternoon** | The corollary's *necessity* (`c_0c_1 ≥ b` is also needed) is not proved: it wants "the `p`-subset sums of `{0..b-1}` are *exactly* an interval", where `pick_sum` gives only the inclusion. Same induction, other direction. |
| ~~**Theorem 6**~~ — the rigorous upper bound on `#nice(b)` | **done** (`adm_of_pandigital`, `countP_pandigital_le_adm`, `countP_pandigital_le_window`) | Costed as "not worth it — an asymptotic statement with error terms. Formalising analytic estimates costs far more than the result is worth." Wrong, and instructively so: **there are no analytic estimates in it and no error term.** `+ O(b^k)` was how the informal account happened to phrase the bound; written with an exact ceiling — `count ≤ window · ⌈len/W⌉`, and even that is only a corollary of the exact count — the whole thing is elementary counting on a periodic predicate, and it cost an afternoon core-only. **Price the statement you would actually prove, not the one the summary table quotes.** |
| ~~**Theorem 6**, the top-digit refinement (condition 4)~~ | **done** (`admTop_of_pandigital`, `countP_pandigital_le_admTop`, `topSlots_const`, `no_pandigital_of_top_clash`) | Costed at "an afternoon", which is what it took — the *first* estimate to land, and the interesting part is that the reasoning behind it was still wrong. It said the work was "exact integer `e`-th roots and their monotonicity". **No root is extracted anywhere in the formalisation.** The roots are where a program evaluating the bound puts the *cuts*; the theorem only needs that where the top quotient agrees at an interval's two ends it is constant between them, which is two divisions and `Nat.div_le_div_right`. **Formalise the property the construction has, not the construction.** What it did need, and what the estimate never mentioned: the length `L` as an explicit parameter (see "Traps"), and the *exact* band rather than §9.4's crude one, which `base_ten_exact_band` gets from the length identity. |
| ~~**Theorems 8, 9 and 10**~~ — the infinitude reduction, the divergence, the conditional | **done** (`infinitude_iff`, `model_diverges`, `conditional_infinitude`, `divergence_is_not_existence`) | Never costed, because "infinitude" reads like an analytic statement and analytic statements were priced out of core. It is not one: the reduction is the crude band read twice, the divergence needs a band lower bound (exhibit an interval, `E ∣ b-2`) and a Stirling substitute (`b^b ≤ 4^b·b!`, two inductions), and both are ℕ arithmetic. An afternoon. **The rule that missed it is the same one Theorem 6 broke** — do not price a formalisation from the word the summary uses for it. |
| ~~**Theorem 1's converse**~~ | **done** (`band_nonempty`, `band_nonempty_iff`) | ~370 lines with no root extraction anywhere: the proof walks `g(n) = len(n^e1) + len(n^e2)` up the integers, which steps by at most 2 once `n ≥ 2·e1·e2`, and a step of 2 forces the dead-class divisibility. The threshold is real: the converse is false below it (80 (pair, base) counterexamples over `e1 ≤ 7, e2 ≤ 8`, the largest at base 24). It had been bundled with the next row as "the same lemma", which hid a cheap job inside an expensive one. |
| **Theorem 9** for *all* admissible bases, not just `E ∣ b-2` | **300–600 lines, no value for infinitude** | The general band lower bound is the plateau of `⌊e1t⌋+⌊e2t⌋`: level sets are intervals between consecutive points of `(1/e1)ℤ ∪ (1/e2)ℤ`, so multiplicative width `≥ b^(1/e1e2)`. Wants exact `ceil_root` in ℕ plus the jump case analysis. Theorem 1's converse needed `\|band\| ≥ 1`; this needs `\|band\| ≥ b^q`, and only the second wants a root. |
| **Coverage is constructive** — for every `b` and every `e` with `gcd(e,b)=1`, infinitely many `n` have every base-`b` digit in `n^e` | **400–700 lines, marginal** | The only *unconditional* infinitude statement in the family. Needs `(Σ d_i Y^i)^e` coefficient-wise (core has no `Polynomial`) and a carry-free concatenation lemma for `digits` (`digits_split` is most of it). It proves a *relaxation*, and the paper proof is four paragraphs — so the argument for doing it is that the file currently contains no existence theorem for a whole family. |
| A second-moment version of **Theorem 10** | **blocked by measurement, not by Lean** | Would weaken `ModelPositive` from positivity to a variance bound. The naive second moment is *wrong*: in exhaustive counts, close pairs of solutions run 1.6× over Poisson at **+46σ**. Model that correlation first. |
| The yield and cost estimates | **not theorems** | They are heuristic expectations under a random-digit model. Lean has nothing to say about them, and pretending otherwise would be the worst kind of false precision. |
| The exhaustive counts | **out of the question** | Would need a verified search and kernel-level evaluation of ~10^16 candidates. |

**Proved is not the same as evaluated.** Theorem 6 proves that the bound's four filters are
**valid**. A program that computes the bound for a given base still has to **evaluate** them
— decompose the band into maximal constancy intervals by exact roots, compose the residue
conditions inside each, and handle the partial window at the end — and a bug in any of that
is invisible to the theorem. So the computed bound is checked separately from the proof.
"The theorem is proved" and "the number is right" are different claims whenever the theorem
is about a filter and the number comes from code.

**Cost the halves, not the proposition.** Theorem 5 was first costed at ~1 month as a single
lump. Split into soundness and completeness it was an hour and an afternoon, because the two
halves need completely different machinery — soundness is one induction over a list,
completeness is a construction. An estimate for a biconditional is an estimate for its
hardest direction, and quoting it for the pair hides whatever is cheap.

**And the constructive half then came in at a day against an estimate of a month, for a
reason worth generalising.** The estimate priced the construction in the vocabulary a
mathematician would reach for — subsets of `{0,…,b-1}`, an explicit permutation, `Finset` —
and concluded that core Lean's lack of that vocabulary was the obstacle. It was the opposite.
Pandigitality here is already `∀ v, occ v (d1 ++ d2) = 1`, `occ` is additive over `++`, and
every step of the construction — splitting a run, dealing blocks into slots, moving the digit
`0` — is then a statement about *counts*, provable by the same `omega` that does the
arithmetic. **Cost a formalisation in the vocabulary the file already has, not in the
vocabulary the paper proof used.**

## Toolchain drift: 4.16 → 4.33 (2026-08-12)

Five errors, two causes, both in core `Nat` and neither touching an argument of the
mathematics:

* **`Nat.pos_pow_of_pos` is gone**, replaced by `Nat.pow_pos`, which takes the exponent
  *implicitly* — so `Nat.pos_pow_of_pos k h` becomes `Nat.pow_pos h` (4 sites). One site
  needed `(a := b) (n := k)` because neither implicit is determined by the expected type
  there.
* **`simpa using hx` stopped closing `b ^ 0 ≤ x` from `0 < x`.** `simp` now normalises the
  goal to `1 ≤ x` and the final `exact` will not take `0 < x` for it, though the two are
  definitionally equal in `Nat`. Replaced with `rw [Nat.pow_zero]; omega`, which does not
  depend on simp's normal form.

The second is the one to remember: a `simpa` that leans on a defeq is a *syntactic*
dependency on whatever simp set ships that month. `omega` after an explicit `rw` is
drift-proof.

Nothing about the proofs changed, and the axiom report is unchanged. **If you see `sorryAx`
in that report, read the errors above it**: Lean emits the `#print axioms` lines regardless,
and a failed proof becomes `sorryAx` rather than silence.

### `elan` makes a fast compile look slow

With the default toolchain set to the **`stable` channel**, the `~/.elan/bin/lean` shim
re-resolves that channel over the network on *every* invocation. On an early, much smaller
revision of the file that was 22 s of wall time against a 0.83 s compile, and
`lean --version` alone took 10 s. The overhead is a fixed per-invocation cost that does not
scale with the file, so the ratio has shrunk as the file grew, but it is still several
seconds of nothing. Do not read the shim's wall time as a proof cost.

The **`lean-toolchain` file** is the fix: it pins `leanprover/lean4:v4.33.0`, so the shim
resolves locally with no network at all. **It only works from this directory.** `elan`
searches for `lean-toolchain` upward from the *current directory*, not from the source file's
directory, so running `lean path/to/NiceNumbers.lean` from anywhere else does not find it and
pays the overhead.

Two other routes if you would rather not rely on the file: `elan default
leanprover/lean4:v4.33.0` to pin the machine-wide default, or call
`~/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean` directly.

Pinning has the usual cost: a toolchain bump is a deliberate edit rather than something
`elan` does for you — which, given that 4.16 → 4.33 broke five lines, is the side to err on.
