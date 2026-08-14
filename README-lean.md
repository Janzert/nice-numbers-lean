# Formalising the nice-number theorems in Lean 4

**Answer to "can any of the proofs be written in Lean?": yes — Theorems A, B, C,
C′, F, G and H and Proposition D are done, they compile in about seven seconds
against Lean core with no Mathlib, and they are strictly stronger than the
exhaustive checks they replace.** Proposition C′ has all three of its parts
here: *soundness* for all bases and all `j`, *unconditional completeness*
**disproved** by a counterexample in the file, and the *conditional* completeness
theorem of REPORT §6.3 proved in full — leading digits and all.

```bash
lean NiceNumbers.lean      # 7.0 s, 4594 lines, no errors, no sorry
```

**Theorem H (2026-08-13) is the first *quantitative* theorem here**, and the first
whose conclusion is a number rather than a yes/no: at most `countP adm` of the band
is nice, where `adm` reads only `n mod (b-1)` and `n mod b^k`. It is also the one
whose *equality case* is the interesting part — `base_ten_nice_iff` says the set of
`(2,3)`-nice numbers in base 10 is exactly `{69}`.

**Theorem F (2026-08-13) is the first *constructive* theorem here**; everything
else was an impossibility. That changes what has to be guarded — see "Non-vacuity"
— and it is the one theorem that did **not** retire or narrow a gate, because
none of the five cases `verify.py`'s gate F runs satisfies its hypotheses.
**Theorem C′ (2026-08-13) is the second constructive one, and by some distance the
largest**: ~1 100 lines, it *does* retire a gate, and it produces an explicit
pandigital pair rather than ruling one out.

Written against 4.16, verified on **4.33**; see "Toolchain drift" below for the
two core renames that cost, and why an `elan`-shimmed `lean` appears to take 20 s
when the compile is 0.8 s.

The file ends with `#print axioms` for every headline theorem. Each reports only
`propext`, `Classical.choice`, `Quot.sound` — Lean's three standard foundational
axioms. No `sorryAx`, and no `native_decide` (which would add
`Lean.ofReduceBool` and move trust into the compiler).

## What is proved

| Lean name | statement | replaces |
|---|---|---|
| `no_nice_of_dvd` | `(e₁+e₂) ∣ e₁*(b-1)` ⟹ `numDigits b (n^e₁) + numDigits b (n^e₂) ≠ b` | `verify.py` gate A's *dead* direction, which checked `e₁ ≤ 8, e₂ ≤ 9, b < 120`. Its converse is not proved and stays in the script |
| `nice_no_solution` | base `b ≡ 1 (mod 5)` has no square/cube candidate | the `(2,3)` instance |
| `one_three_no_solution` | base `b ≡ 1 (mod 4)` has no `(1,3)` candidate | the `(1,3)` instance |
| `two_four_no_solution` | base `b ≡ 1 (mod 3)` has no `(2,4)` candidate | the `gcd > 1` instance |
| `no_nice_of_mod_four` | for **every** pair `e₁,e₂ ≥ 1`, base `b ≡ 3 (mod 4)` fails the digit-sum identity | — |
| `residues_empty_of_mod_four` | same obstruction as the sieve states it: `R_b = ∅` for `b ≡ 3 (mod 4)`, every pair | `verify.py` gate B, which checked `e₁ ≤ 8, e₂ ≤ 9, b < 400` |
| `base_unique` / `bands_disjoint` | **Prop D** — the length identity holds for at most one base, so distinct bases' bands are disjoint | `verify.py` gate D, which checked five pairs, `b < 500`, ~2700 values of `n` |
| `no_nice_of_universal_clash` | **Theorem G**, operative half — a base where `x^e₁ ≡ x^e₂ (mod b)` for every `x` has no pandigital `n` | — |
| `clash_iff_dvd_clashMod` | **Theorem G**, classification — the clashing bases are exactly the divisors of `N(e₁,e₂)`, computed as a finite gcd | `verify.py` gate G's scan over `b < 200`, `e₁ ≤ 5, e₂ ≤ 7` |
| `clash_prime_pow_iff` / `prime_pow_dvd_clashMod_iff` | **Theorem G**, local criterion — `p^a ∣ N` iff `a ≤ e₁` and every unit mod `p` has order dividing `e₂-e₁` | — |
| `valOf_mod_wsum` / `valOf_mod_pow_sub_one` | **Prop C′**, the engine — mod `b^j - 1` a digit list is worth `Σ_t b^t S_t`, the totals of its positions `≡ t (mod j)`. All `b`, all `j`, all lists | the block-sum half of `verify.py` gate C′, which sampled 200 000 shuffles at `j = 2,3` |
| `valOf_mod_pred` / `sieve_sound` | **Prop C′**, soundness — casting out `b-1`s, hence `I(m) ⊆ {z ≡ T mod gcd(m,b-1)}` for every modulus | — |
| `base_four_sieve_is_incomplete` | **Prop C′ is false** — base 4, lengths `(2,2)`: no pandigital pair has `x+y ≡ 2 (mod 5)`, though `gcd(5,3) = 1` means the digit sum permits it | nothing; this one *refutes* a claim the report used to make |
| `theorem_C_prime` | **Theorem C′** (REPORT §6.3) — where the class sizes admit a legal `p` with the no-gap conditions, and are big enough, **every** residue the digit-sum congruence permits is the sum of a genuine pandigital pair of those digit lengths, leading digits included. All bases, all `j`, all lengths, all `p` | `verify.py` gate C′(a), which checked four `(b, L1, L2, j)` rows through `block_image` — a *weaker* statement, since that DP ignores the leading-digit rule |
| `blocks_hit` | **Theorem C′**, block level — the same conclusion about `Σ_t b^t S_t`, with no digit lengths and no leading digits in the statement | — |
| `pick_sum` | **Theorem C′**, engine 1 — the `p`-element sublists of a run of `p+q` consecutive integers realise every sum in `[min, min + pq]`, with no gaps | — |
| `cover_exists` | **Theorem C′**, engine 2 — mixed-radix covering: if each place `b^t` opens before the lower places run out, `{Σ ν_t b^t : ν_t ≤ N_t}` is a full interval | — |
| `blk_identity` | **Theorem C′**, the join — an identity in `ℕ`, not a congruence: `X + (b-1)·Σ_t b^t σ_t + (b^j-1)·τ_{j-1} = Σ_t b^{t+1}·ΣA_t` | — |
| `residues_nonempty_iff` / `residues_empty_iff` | **Theorem C** — `R_b = ∅` iff `a = 1`, or (`a ≥ 3` and `e₂-e₁` even and `e₁ ∤ a-1`), where `a = v₂(b-1)`. All bases, all pairs | nothing; §4 of the report had no gate, and now needs none |
| `residues_single_nonempty_iff` | **Theorem C**, single exponent — `R_b ≠ ∅` iff `a = 0` or `e ∣ a-1`. This is the family §14 recommends searching | the base list §14 quoted from a scan |
| `no_nice_of_two_adic` | **Theorem C**, operative form — a base in a dead 2-adic class admits no `n` satisfying the digit-sum identity | — |
| `residues_empty_of_mod_four_of_C` | **Theorem B is the `a = 1` case of C**: `b ≡ 3 (mod 4)` is exactly `v₂(b-1) = 1`. Not a replacement — C assumes `e₁ < e₂`, B does not, so the degenerate `e₁ = e₂` stays B's alone | — |
| `add_pow_ladder` / `slot_step` | **Theorem F**, the engine — `(r + x·bⁱ)^e ≡ r^e + e·r^{e-1}·x·bⁱ (mod b^{i+1})` for `i ≥ 1`, and hence that adding digit `x` at level `i` moves slot `i` of `n^e` along an arithmetic progression with difference `e·r^{e-1} (mod b)`. This is the recurrence the CUDA and Vulkan kernels advance the digit with, and the "2 slots per digit" law itself | nothing; the repo asserted the ladder in comments and in three kernels |
| `exists_good_digit` | **Theorem F**, the pigeonhole — two maps injective on `{0,…,b-1}` colliding at most once leave a nonzero digit avoiding a list `U` in both, once `2\|U\| + 2 < b` | — |
| `greedy_distinct_slots` | **Theorem F**, slot form — some `d`-digit `n` has `2d` pairwise-distinct values among the low `d` slots of `n^{e₁}` and `n^{e₂}` | — |
| `theorem_F` | **Theorem F** — hence combined digit deficiency `≤ b - 2d`, i.e. `b(1 - 2/E)` since `d ≈ b/E` | nothing; gate F stays, see below |
| `no_even_base` | **Theorem F**, its limit — an even base admits no `β`, so Theorem F covers only odd bases. All the repo's `(1,3)` targets are even | a scan that had found only the boundary |
| `pandigital_length` / `pandigital_digitSum` | **Theorem H**, the bridge — pandigitality *implies* the two numerical consequences §1–§3 take as hypotheses, so H is a statement about nice numbers and not about numbers assumed to behave like them | nothing; the file had asserted the implication only at 69 |
| `pandigital_pow_bounds` | **Theorem H**, the band without roots — `b^(b-2) ≤ n^E < b^b` for every pandigital `n`, by multiplying the two per-exponent length bounds. No jump structure, no `gcd`, no exponents in the statement | nothing |
| `theorem_H` | **Theorem H** — every pandigital `n` is in that band and passes `adm`, a test reading only `n mod (b-1)` and `n mod b^k`. All bases, all pairs, all `k`, all `n` | nothing; gate H stays and checks the *other* half, see below |
| `countP_run_le` / `adm_period` | **Theorem H**, the closed form — `adm` has period `(b-1)·b^k`, and a periodic test on a segment is counted by one window times `⌈len/W⌉` | — |
| `theorem_H_count` / `theorem_H_closed` | **Theorem H**, counting and closed forms — `#{nice in band} ≤ countP adm (band) ≤ countP adm (one window) · ⌈len/W⌉` | — |
| `base_ten_nice_iff` | **The set of `(2,3)`-nice numbers in base 10 is exactly `{69}`** — the sharpness witness for H, and the only equality case known | nothing; the repo had this from a 53-number scan, never as a theorem |

All of these hold for **all** naturals, and the three gates named above **have been
deleted** from `verify.py` (which is now ~38 s: gate H put back rather more
than the deletions took out). Gate G was
**narrowed** instead of deleted, for the reason the next paragraph gives: what is
left of it is `N_λ = N_gcd`, the one step the Lean statement routes around.

**`residues_empty_of_mod_four` exists because of that deletion.** Gate B did not
check the digit-sum identity that `no_nice_of_mod_four` refutes — it checked that
the *residue set* `R_b = {ρ : ρ^e₁+ρ^e₂ ≡ T (mod b-1)}` is empty, which is the
form the sieve actually uses and which the digit-sum theorem does not literally
imply (it assumes a solution's digit sums, not a bare congruence class). Same
two-line parity argument, stated over the congruence instead. **When deleting a
finite check in favour of a proof, compare the two statements, not the two
section headings** — the check is usually of some *proxy* for the theorem, and the
proxy is what the rest of the code depends on.

`numDigits` and `digitSum` are defined from scratch by repeated division
(60 lines, including `bounds_of_numDigits`: `numDigits b x = k+1 ↔ b^k ≤ x < b^(k+1)`,
and `digitSum_mod`: casting out `b-1`s). Nothing about digits is assumed. §5 adds
`digits` (the digit *list*) and `Pandigital` — the first time the file states the
solution condition itself rather than one of its two numerical consequences,
because a digit *collision* is invisible to both of them.

## Non-vacuity — the check that matters most

An impossibility theorem with contradictory hypotheses proves itself. §4 of the
file rules that out, kernel-checked:

* `length_identity_holds : numDigits 10 (69^2) + numDigits 10 (69^3) = 10`
* `digitsum_identity_holds : 2 * (digitSum 10 (69^2) + digitSum 10 (69^3)) = 10 * (10-1)`

i.e. 69 in base 10 — the only known nice number — satisfies both hypothesis
families. Then two theorems shown *firing*: `base_eleven_dead` (Theorem A at
`b = 11`) and `base_seven_dead` (Theorem B at `b = 7`, where Theorem A says
nothing because `7 ≢ 1 mod 5`), plus `base_seven_dead'` at exponents `(3,8)` to
show B really is pair-independent.

Prop D needs the same guard for the opposite reason — "at most one base" is
trivially true of an `n` that has none. `sixtynine_in_band : InBand 10 2 3 69`
supplies the witness, and `sixtynine_only_base_ten` then reads off that base 10 is
the *only* base 69 is a candidate in, over all bases at once and with no finite
search.

**Theorem H needs the guard in a third shape again: an upper bound is vacuous when
it is not attained, and useless when the thing it bounds is empty.** Both are
answered at once by `base_ten_nice_iff` — the bound is 1, the truth is 1, and 69 is
the witness. The second witness, `base_seventeen_bound` (`≤ 585` from a 272-number
window over a band of 10 347), is there because base 10 is the wrong shape to
exercise the closed form at all: `W = 90 000` against a band of 60.

**Which filter each witness actually covers is not obvious and had to be measured.**
At base 10 with `k = 4` the low slots alone already pin 69, so `base_ten_survivors`
survives deleting `resOK` from `adm` — it is `base_seventeen_window` that catches
that deletion. Three other mutations (depth `k = 3` instead of `4`, deleting
`lowOK`, widening the band by moving `lo` from 39 to 30) are each rejected by the
base-10 witness. A witness that passes under a deleted hypothesis is not a witness
for that hypothesis, and only running the mutation says which is which.

Theorem G needs the guard twice over, because it introduces a *definition*:

* `sixtynine_pandigital : Pandigital 10 2 3 69` — the definition is satisfiable,
  so `no_nice_of_universal_clash` is not refuting the empty set. (`digits 10 4761
  = [1,6,7,4]`, `digits 10 328509 = [9,0,5,8,2,3]`, ten values, each once.)
* `base_ten_no_clash : ¬ UniversalClash 10 2 3` — and Theorem G had better *not*
  kill base 10, or it would contradict 69. `N(2,3) = 2` and `10 ∤ 2`.

Then two theorems shown firing where A and B say nothing at all:
`one_three_base_six_dead` (base 6 is `2 mod 4`, so A misses it, and even, so B
misses it — but `x ≡ x³ mod 6` always) and `two_four_base_twelve_dead`. Plus
`clash_three_one_three` and `nine_no_clash_one_three`, which run the local
criterion forwards and backwards on numerals.

**Theorem C's guard is the sharpest of the lot, because it is a biconditional:
both directions have to be shown firing, or the theorem could be the constant
`False` or the constant `True`.**

* `two_four_base_seventeen_dead` — `(2,4)` at base 17, where **A, B and G all say
  nothing** (`17 % 3 = 2`, `17 % 4 = 1`, `17 ∤ N(2,4) = 12`) and C kills it alone.
* `two_four_base_thirtythree_live` — base 33, one step up in `v₂(b-1)`, is *not*
  killed, and the witness `ρ = 4` the theorem names is checked by `decide`. So the
  `e₁ ∣ a-1` boundary is sharp, not slack.
* `base_ten_live` / `base_ten_residue` — base 10 had better be alive, or C would
  contradict 69; and 69 itself is exhibited as a residue.
* `single_four_base_twentynine_dead` / `single_four_base_thirtythree_live` — the
  same pair of ends for the single-exponent form, on the two bases §14 of the
  report names.

Six statement-level mutations were checked and all six are rejected: declaring
base 33 dead the way base 17 is, weakening `a ≥ 3` to `a ≥ 2`, dropping the
`e₂-e₁` odd clause, widening `a ≤ 2` to `a ≤ 3`, moving the odd-gap witness from
`(b-1)/2 - 1` to `(b-1)/2 + 1`, and (single exponent) `e ∣ a` for `e ∣ a-1`.

**Theorem C′ needs the same kind of guard as C, and it caught a real bug.** Its
hypothesis is a conjunction of no-gap inequalities, and the first version stated
them for *every* `t` rather than `t < j`. That type-checks and it is
**unsatisfiable** — `b^t` outruns any fixed `Σ_{s<j} N_s b^s` — so the theorem was
vacuous while looking correct. Nothing but a witness finds that.

* `base_ten_j_two_complete` — base 10, `j = 2`, digit lengths `(4,6)`: the lengths
  of `69² = 4761` and `69³ = 328509`. `c = (5,5)`, `p = (5,0)`, `N = (25,0)`, and
  the conclusion is that every residue mod `99` allowed by casting out 9s is the
  sum of a genuine pandigital `(4,6)` pair. All the hypotheses discharge by
  `decide`.
* `base_ten_j_five_rider_fails` — and at `j = 5`, which is exactly where base 10's
  sieve *does* gain (`11111 = 41·271` has order 5 and misses two residues), the
  class sizes are `(3,2,2,2,1)` and the `c_t ≥ 2` half of the rider fails. The
  theorem stops precisely where the counterexample starts.
* `base_four_rider_fails` / `base_four_clears_the_other_half` /
  `base_four_clears_the_no_gap` — base 4, lengths `(2,2)`, is the sharper test: it
  clears `c_t ≥ 2` **and** the no-gap conditions (`p = (2,0)` gives `N = (4,0)`,
  `b^1 = 4 ≤ 5`, `K-1 = 4`), both by `decide`, and is stopped only by `c_t ≥ 3` at
  the class carrying the second number's leading slot. Checking what it *passes* is
  the point: a witness that fails several hypotheses at once says which one is
  load-bearing only if the others are shown to hold. Without that
  clause the theorem would contradict `base_four_sieve_is_incomplete`, three
  sections earlier in the same file. **Both halves of the rider are load-bearing,
  and each is pinned by a witness that fails on it alone.**

**Theorem F needs a guard the other five do not, because it is the only
constructive one.** An impossibility theorem is worthless if its hypotheses are
contradictory; a *construction* is worthless if its conclusion is free. Both are
checked:

* `F_base_thirteen`, `F_base_sixtyfive`, `F_base_fortyseven` — the hypotheses are
  satisfiable, at `(2,3)` bases 13 and 65 and at `(1,3)` base 47, each with the
  `ρ` and `β` the theorem asks for supplied as numerals and every side condition
  closed by `decide`. Base 65 forces 26 of its 65 digit values to occur.
* `F_conclusion_not_automatic` — `169 = 13²` lies inside the very interval
  `F_base_thirteen` quantifies over and **fails** the bound: `169² = 13⁴` and
  `169³ = 13⁶`, so between them they show two digit values and miss eleven. The
  conclusion is a selection, not a property of the range.
* `deficiency_sixtynine : deficiency 10 2 3 69 = 0` — the definition means what
  it says, checked against the one number in the repo that is known to miss
  nothing.
* `no_even_base`, `base_thirtyfour_is_even`, `base_fiftyseven_not_coprime` — the
  two `(2,3)` bases this repository benchmarks are **outside** the theorem, and
  the file says so rather than leaving it to be discovered. The first of those is
  a theorem about every even base, not a remark about 34.

Fourteen mutations were checked and all fourteen are rejected. The four that
matter: weakening any of the three counting budgets (`4(d-1)+2 < b` in the
theorem, `4i+2 < b` in the step, `2|U|+2 < b` in the pigeonhole) from `<` to `≤`;
dropping the leading-digit guard from the bad set; dropping the collision term
from the bad set; and dropping the factor `e` from the ladder's slope. Also
rejected: each of `hstart`, `hβ`, `hce₁`, `hcρ` replaced by a triviality, the
conclusion strengthened to `2d+1`, a perturbed `β` in a witness, and a witness
pushed one level past its counting bound.

## The formalisation improved the mathematics

The proof of Theorem A in [`REPORT-provability.md`](../../REPORT-provability.md) goes through
`f(t) = ⌊e₁t⌋ + ⌊e₂t⌋`, its jump points `j/e₁` and `i/e₂`, which of them
coincide, and a `gcd` bookkeeping step. None of that survives contact with Lean,
and it turns out none of it is needed. The Lean proof is:

1. `b^a ≤ n^e₁` and `n^e₂ < b^(c+1)` both bound the same quantity `n^(e₁e₂)`,
   giving `a·e₂ < (c+1)·e₁`. Run it the other way for `c·e₁ < (a+1)·e₂`.
   Those two confine `(a,c)` to a window of width exactly `e₁+e₂`.
2. The length identity turns the window into `E·k < E·(a+1) < E·(k+1)` where
   `E = e₁+e₂` and `k` is the cofactor from the divisibility hypothesis, which
   forces `k < a+1 < k+1`.

No floors, no reals, no `gcd`, no case analysis — and the hypothesis is the
single divisibility `(e₁+e₂) ∣ e₁*(b-1)`, which is *sharper to state* than
`b ≡ 1 mod (e₁+e₂)/gcd(e₁,e₂)` and equivalent to it. §2 of the main report
should be rewritten to use this argument.

**Prop D went the same way, and further.** §7 of the report calls it "a routine
exercise from the exact endpoints `b^{j/e1}`, `b^{i/e2}`", and the estimate above
said "same window technique as A, ~1 day". Neither the endpoints nor the window
are needed, and it took an afternoon. `numDigits b x` is *antitone in `b`*
(`b^k ≤ b'^k`, so a length bound in the larger base is one in the smaller), hence
`numDigits b x + numDigits b y − b` is **strictly decreasing in `b`** and vanishes
at most once. That is the whole proof — three short lemmas, `omega` closing each
branch of a trichotomy.

Two consequences of proving it that way. It never mentions `e₁`, `e₂` or `n`, so
the theorem is about *any two values* `x, y`: `base_unique` covers every exponent
pair, including ones nobody has tabulated, and `InBand`/`bands_disjoint` are the
`(e₁,e₂)` corollary rather than the content. And it is strictly stronger than the
crude interval argument the report contrasts it with, which only ever gave `≤ 2`
bases. **The lesson repeats A's: the informal proof reached for the sharp
endpoints because they were already derived and sitting there, and the sharp
endpoints were the reason it looked like a day's work.**

**Theorem C was priced at "Hensel plus the structure of `(ℤ/p^k)ˣ`", and needed
neither — nor the CRT, nor a single odd prime.** The estimate came from the
report's own framing: `R_b = ∅` iff the congruence is unsolvable modulo some
`p^a ‖ b-1`, so decide it prime power by prime power. That framing is true and it
is the expensive way round. Three things collapse it:

1. **Odd prime powers never obstruct, because `ρ = 0` solves them.** `2T = b(b-1)`
   makes `T ≡ 0` modulo the odd part of `b-1`, so the local congruence there is
   `ρ^{e₁} + ρ^{e₂} ≡ 0`. Everything is 2-adic, which the report had *observed*
   empirically ("all 2-adic") without noticing it was forced.
2. **At 2 the question is a valuation count, not a solvability question.**
   `T ≡ 2^{a-1} (mod 2^a)`, and `S ≡ 2^{a-1} (mod 2^a)` iff `v₂(S) = a-1`
   *exactly*. So one only has to ask which valuations `ρ^{e₁}(1 + ρ^{e₂-e₁})` can
   have — three cases, three clauses, no group structure anywhere.
3. **Writing the witnesses down removes the CRT.** The half that looks like it
   needs assembly ("solvable locally everywhere ⟹ solvable") is discharged by
   four explicit residues. The `e₂-e₁` odd witness is the one that makes this
   work: `(b-1)/2 - 1` is `-1` mod the odd part, not `0`, and the opposite
   exponent parities cancel the sign. Insisting on a witness that is `0` there is
   what forces an inverse, and an inverse is what forces CRT.

**The lesson is the same one A, D and G taught, and this is its fourth outing:
the informal proof reached for the machinery that would decide the *general*
local question, when the specific local question had a one-line answer.** Every
estimate in the table below that was written from an informal proof sketch has so
far been too pessimistic, and always for this reason.

**Theorem G was priced at a week "because it needs Carmichael `λ`", and `λ` turned
out to be in the *statement*, not in the proof.** The estimate in the table below
used to say the sufficiency half was the only cheap piece. In fact all of G went
through in an afternoon, core-only, once three things were noticed:

1. **`λ(p^a) ∣ d` is an evaluation, not a hypothesis.** What the argument actually
   uses is "every unit mod `p` has order dividing `d`". State the criterion that
   way (`clash_prime_pow_iff`) and the Carmichael function disappears from the
   theorem entirely; it reappears only if you want to *compute* the answer.
2. **The global statement needs no CRT and no factorisation.** `b` clashes iff
   `b ∣ x^{e₂} - x^{e₁}` for every `x`, so the clashing bases are the divisors of
   `G = gcd_x (x^{e₂} - x^{e₁})` by definition — divisor-closure, lcm-closure and
   boundedness all at once. The `x = 2` term bounds every clashing base by
   `2^{e₂} - 2^{e₁}`, which also truncates the gcd to a finite one, so `N` becomes
   a *computation the kernel can do* (`clashMod 3 7 = 120` by `decide`, no axioms
   at all). The report's proof assembles the local criteria by CRT; it never needs to.
3. **Sufficiency needs the dichotomy `p ∣ x` or not, not the splitting
   `x = p^v u`.** If `p ∣ x` then `p^a ∣ p^{e₁} ∣ x^{e₁}` and both powers vanish;
   otherwise `x` is a unit. The valuation `v` is never used.

The gcd form is also the better *definition* outside Lean: `verify.py`'s
`universal_bound` iterates a hardcoded prime list `[2..47]`, which is silently
wrong once `e₂ - e₁ ≥ 47`, while the gcd form has no such parameter. Gate G now
checks the two against each other, which is exactly the step Lean routes around.

**Theorem F was priced at "~2 weeks, the bookkeeping is not small", and cost an
afternoon — but for the opposite reason to A, C, D and G.** Those four were
overpriced because the informal proof reached for machinery it did not need.
Theorem F was overpriced because the informal *statement* was not yet a theorem,
and once it was made into one the proof was short. Three things came out of
making it precise, and two of them are corrections to §8 of the report:

1. **The side condition is a hypothesis about one number, not an `O(db)` check.**
   The report says at most `2·|Used|` digits are killed "plus the `x` for which
   the two new digits coincide" — *the* `x`, singular, which is true only when
   `α_{e₁} - α_{e₂}` is a unit mod `b`, and the report flags this as a side
   condition "which is `O(db)`". But `α_e = e·r^{e-1} (mod b)` depends on `r` only
   through `r mod b`, and `r mod b` is the **starting digit `ρ`, fixed at level 0
   and never touched again**. So the condition is one check per candidate `ρ`,
   `O(b)` in total, not one per level. In Lean it becomes a unit `β` with
   `e₂ρ^{e₂-1} + β ≡ e₁ρ^{e₁-1}`, carried as a hypothesis and discharged by
   `decide` at each witness base.
2. **The counting bound is `E ≥ 4`, not `E ≥ 5`.** The report gets `4b/E < b` by
   rounding `d ≈ b/E` and concludes the bound "fails for `E = 3, 4`". The exact
   condition is `4(d-1) + 2 < b`; at `E = 4` that is `≈ b - 2 < b` and it
   **holds**. `(1,3)` clears it at bases 7, 11, 19, 23, 31, 35, 43, 47, 55, 59
   and 67 — `F_base_fortyseven` is base 47 — and misses at base 46 by exactly
   zero (`4·11 + 2 = 46`). `E = 3` never clears it. So the honest statement is
   that `E = 4` is marginal and base-dependent, not dead.
3. **`gcd(e₁e₂, b) = 1` is where the theorem actually stops, and it is worse than
   the report suggests: no even base is ever covered.** That is
   `no_even_base`, proved rather than observed — an even `b` forces both
   exponents and `ρ` odd, hence both `α_e = e·ρ^{e-1}` odd, hence an even gap,
   hence no unit `β`. So the whole `(1,3)` family this repo searches (bases 38,
   40, 42, 46) is out, and so is `(2,3)` base 34; `(2,3)` base 57 is odd but
   loses the coprimality instead. Over all ten pairs with `e₂ ≤ 5` and bases
   `< 70` the theorem fires at 174 (pair, base) instances, **every one at an odd
   base**. This is why gate F survives where gates A, B and D did not: it is not
   a weaker version of the theorem, it is the *only* evidence for the cases the
   theorem cannot reach. Scanning found the boundary; proving it is what turned
   "34 and 57 happen to be out" into "every even base is out, necessarily".

**Why not Mathlib, when it was on the table.** The offer was taken seriously and
declined on measurement, not principle. What Mathlib would have supplied is
`Finset` counting; what the proof actually needs is six list lemmas
(`countP` subadditivity, `countP ≤ 1` under a uniqueness hypothesis, `countP` of
a membership test bounded by the list's length, `countP p + countP ¬p = length`,
`countP > 0 → ∃`, and `countP = (filter).length`) totalling about 60 lines — and
the one lemma that would have been genuinely painful to redo,
`List.Nodup.length_le_of_subset`, is **already in core**. Against that: a
lakefile, a multi-gigabyte pinned dependency, and a compile going from 4 s to
minutes, for a file whose stated value is having nothing that can rot. Two core
gaps are worth knowing about if this is revisited: **`by_contra` and `set` are
Mathlib tactics** (`rcases`, `obtain` and `rintro` are core), and there is no
`ring` — the ladder's polynomial identity is closed by `simp` with the
associativity/commutativity lemmas after generalising `r^{e-1}` out.

**One kernel trap, and it is `digits`' fault, not Theorem F's.** `digits` is
defined by well-founded recursion, so it does not reduce in the kernel and
`decide` cannot evaluate anything built on it. `deficiency_sixtynine` and
`F_conclusion_not_automatic` therefore route through explicit `digits_step`
chains, exactly as §5's `digits_69sq` already did. The error is legible
(`reduction got stuck at the Decidable instance`), but it appears only at the
`decide`, a long way from the definition that caused it.

## What else is formalisable, and what it would cost

| result | verdict | notes |
|---|---|---|
| ~~**Prop D**~~ — bands for distinct bases are disjoint | **done** (`base_unique`, `bands_disjoint`) | Estimated at ~1 day by the window technique; cost an afternoon by antitonicity of `numDigits` in the base, and came out pair-independent. See above. |
| ~~**Theorem C**~~ — classification of `R_b = ∅` | **done** (`residues_nonempty_iff`, `residues_empty_iff`, `residues_single_nonempty_iff`) | Costed here as "easy per pair, hard in general — needs Hensel plus the structure of `(ℤ/p^k)ˣ`, Mathlib-scale, ~1 week per family". Wrong on every count: it is a closed form in `v₂(b-1)`, no odd prime enters, and it cost an afternoon core-only. See below. |
| ~~**Theorem G**~~ — `q₁(b)=0 ⟺ b ∣ N(e₁,e₂)` | **done** (`no_nice_of_universal_clash`, `clash_iff_dvd_clashMod`, `clash_prime_pow_iff`) | Estimated at ~1 week "needs Carmichael `λ`"; cost an afternoon once `λ` was pushed out of the statement. See above. **What is left is one classical evaluation**: `exponent((ℤ/p^aℤ)ˣ) = λ(p^a)`, i.e. the structure theorem for that group. Mathlib has `Monoid.exponent`; the value at `p^a` would still have to be proved, and only the *closed form* for `N` depends on it. |
| ~~**Theorem F**~~ — the `2/E` greedy bound | **done** (`greedy_distinct_slots`, `theorem_F`) | Estimated at "medium-hard, ~2 weeks" for the digit ladder plus a greedy pigeonhole induction; cost an afternoon, and the ladder and the pigeonhole were both short. What the estimate missed is that the *statement* needed two repairs first — the side condition is `O(b)` not `O(db)`, and the counting bound reaches `E = 4`. See above. |
| ~~**Prop C′**, soundness~~ — the sieve never sees more than `Σ_t b^t S_t` | **done** (`valOf_mod_wsum`, `sieve_sound`) | Estimated inside a "~1 month" for the whole proposition; the soundness half cost an hour, because it is an induction on a list and needs no combinatorics at all. |
| ~~**Prop C′**, completeness~~ — no modulus adds density | **done: it is FALSE** (`base_four_sieve_is_incomplete`) | 256-case kernel `decide` on base 4, lengths `(2,2)`. Both natural mutations of the check are rejected, and `base_four_attained` supplies the three witnesses, so it is neither vacuous nor slack. |
| ~~**Prop C′**, the conditional theorem (REPORT §6.3)~~ | **done** (`theorem_C_prime`) | Costed here as "hard, ~1 month", on the grounds that it needs the arena as an *explicit permutation* of `{0,…,b-1}` and core has no `Finset`/`Multiset`. It cost a day. The premise was right and the conclusion wrong: **the absence of `Finset` is what made it cheap, not expensive.** `occ v : List Nat → Nat` is additive over `++`, so "is a permutation" is `∀ v, occ v l = 1` and every step of the construction is an arithmetic identity about counts — no `Perm`, no quotient, no `Multiset.map` congruence lemmas. Reaching for the set-theoretic vocabulary is what would have cost a month. |
| **Prop C″** — the sharp `c_t ≥ 2` form (REPORT §6.5) | **not yet a proof at all** | Open on paper first. Formalising is not the bottleneck — though formalising C′ did shorten the distance: the rider it actually needs is `c_t ≥ 2` everywhere plus `c_t ≥ 3` at one named class, so C″ is one class away rather than `j`. |
| **Prop C′**, descent to a general modulus | **an afternoon, low value** | The theorem is proved at `b^j - 1`; getting `I(m) = {z ≡ T mod gcd(m,b-1)}` for every `m` of order `j` is one CRT step. Core has no CRT, so it is a real if small job, and it changes nothing operational. |
| **Prop C′**, the `j = 2` converse | **an afternoon** | The corollary's *necessity* (`c_0c_1 ≥ b` is also needed) is not proved: it wants "the `p`-subset sums of `{0..b-1}` are *exactly* an interval", where `pick_sum` gives only the inclusion. Same induction, other direction. |
| ~~**T4**~~ — the rigorous upper bound on `#nice(b)` | **done** (`theorem_H`, `theorem_H_count`, `theorem_H_closed`) | Costed here as "not worth it — an asymptotic statement with error terms. Formalising analytic estimates costs far more than the result is worth." Wrong, and instructively so: **there are no analytic estimates in it and no error term.** `+ O(b^k)` was how REPORT §11 happened to phrase the bound; written with an exact ceiling — `count ≤ window · ⌈len/W⌉`, and even that is only a corollary of the exact count — the whole thing is elementary counting on a periodic predicate, and it cost an afternoon core-only. **Price the statement you would actually prove, not the one the summary table quotes.** |
| Part II's yield and cost numbers | **not theorems** | They are heuristic expectations under a random-digit model. Lean has nothing to say about them, and pretending otherwise would be the worst kind of false precision. |
| The exhaustive counts (`(1,3)` has exactly one solution in bases ≤ 44) | **out of the question** | Would need a verified DFS and kernel-level evaluation of ~10¹⁶ candidates. |
| **Theorem H**, the top-digit refinement (REPORT §9, condition 4) | **an afternoon, real value** | The only part of the bound Lean does not have. It needs the band split into maximal intervals on which `⌊n^e / b^(L-h)⌋` is constant, i.e. exact integer `e`-th roots and their monotonicity — none of which is hard, but none of which the file currently has. Worth a factor of 2–3 at the frontier. Until then `verify.py` gate H is what stands behind it. |

**Net effect.** Theorem H added a gate rather than retiring one, and for a reason
worth naming: the Lean theorem covers three of the bound's four filters for all
bases, all pairs and all `k`, but not the fourth, so gate H is not a finite
re-check of anything Lean proves — it checks the top-digit half, and two
properties of `nice-count`'s output (that `B(k=d,h=0)` *equals* the DFS leaf
count, and that the bound holds of every count the repo has measured) that are
not statements about the theorem at all. Four of `verify.py`'s gates are now theorems for all inputs
rather than checks over a finite range, so they are gone from the script rather
than merely superseded: A's dead direction, B, D, and — as of 2026-08-13 — C′'s
conditional-completeness sub-gate. A fifth, gate G, is narrowed to the single
arithmetic identity `N_λ = N_gcd`. Gate C′ itself was **rewritten rather than
narrowed** a day earlier, because formalising its soundness half exposed that the
completeness half it had been sampling is false; what is left of it now is the
conjecture and the counterexample table, both of which Lean does not carry.
Two caveats worth keeping in view: Theorem A's *converse* (every base outside the
dead class really does have candidates) is **not** proved and stays an empirical
check, and neither is the closed form for `N`, for want of `λ(p^a)`. Theorem C
arrived with a gate rather than replacing one, and that gate checks §4.1's
*decoding* — which of C's dead classes Theorem A did not already have — which is
a statement about two theorems at once and so not something either one proves.
**Theorem F changes none of that.** It is the first theorem here that leaves its
gate exactly where it found it, and the gate now *asserts* the disjointness —
sub-gate (b) checks that all five of its cases fail a hypothesis of `theorem_F`,
so the day someone tightens the theorem, the gate says so rather than silently
duplicating it.

**The "no cheap piece left on the shelf" claim in the previous revision was
wrong, and wrong in an instructive way.** C′ was costed at ~1 month as a single
lump. Split into soundness and completeness it was an hour and an afternoon,
because *the two halves need completely different machinery* — soundness is one
induction over a list, completeness is a construction in a combinatorial category
core Lean has no vocabulary for. The lesson is to cost the halves, not the
proposition: an estimate for a biconditional is an estimate for its hardest
direction, and quoting it for the pair hides whatever is cheap.

**And the third piece of C′ then came in at a day against an estimate of a
month, for a reason worth generalising.** The estimate priced the construction in
the vocabulary a mathematician would reach for — subsets of `{0,…,b-1}`, an
explicit permutation, `Finset` — and concluded that core Lean's lack of that
vocabulary was the obstacle. It was the opposite. Pandigitality here is already
`∀ v, occ v (d₁ ++ d₂) = 1`, `occ` is additive over `++`, and every step of the
construction — splitting a run, dealing blocks into slots, moving the digit `0` —
is then a statement about *counts*, provable by the same `omega` that does the
arithmetic. **Cost a formalisation in the vocabulary the file already has, not in
the vocabulary the paper proof used.**

## Toolchain drift: 4.16 → 4.33 (2026-08-12)

Five errors, two causes, both in core `Nat` and neither touching an argument of
the mathematics:

* **`Nat.pos_pow_of_pos` is gone**, replaced by `Nat.pow_pos`, which takes the
  exponent *implicitly* — so `Nat.pos_pow_of_pos k h` becomes `Nat.pow_pos h`
  (4 sites). One site needed `(a := b) (n := k)` because neither implicit is
  determined by the expected type there.
* **`simpa using hx` stopped closing `b ^ 0 ≤ x` from `0 < x`.** `simp` now
  normalises the goal to `1 ≤ x` and the final `exact` will not take `0 < x` for
  it, though the two are definitionally equal in `Nat`. Replaced with
  `rw [Nat.pow_zero]; omega`, which does not depend on simp's normal form.

The second is the one to remember: a `simpa` that leans on a defeq is a
*syntactic* dependency on whatever simp set ships that month. `omega` after an
explicit `rw` is drift-proof.

Nothing about the proofs changed, and the axiom report is unchanged — only
`propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`. **If you see
`sorryAx` in that report, read the errors above it**: Lean emits the `#print
axioms` lines regardless, and a failed proof becomes `sorryAx` rather than
silence.

### `elan` makes a 0.8 s compile look like a 20 s one

With the default toolchain set to the **`stable` channel**, the `~/.elan/bin/lean`
shim re-resolves that channel over the network on *every* invocation: 22 s wall
against 1.7 s of CPU, and `lean --version` alone takes 10 s. The compile itself is
**0.83 s**. Do not read the shim's wall time as a proof cost.

The **`lean-toolchain` file in this directory** is the fix, and it is why the
timing at the top of this file is honest: it pins `leanprover/lean4:v4.33.0`, so
the shim resolves locally and `lean NiceNumbers.lean` takes 0.82 s with no
network at all.

**It only works from `cd lean/`.** `elan` searches for `lean-toolchain` upward
from the *current directory*, not from the source file's directory — so
`lean nice-provability/lean/NiceNumbers.lean` run from the repo root does not
find it and pays 7.9 s. Run it from here. (The file deliberately does not go at
the repo root: this is a Rust/Python repo with one Lean directory in it, and a
root `lean-toolchain` would claim otherwise.)

Two other routes if you would rather not have the file: `elan default
leanprover/lean4:v4.33.0` to pin the machine-wide default (0.036 s for
`--version`), or call
`~/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean` directly.

Pinning has the usual cost: a toolchain bump is now a deliberate edit here
rather than something `elan` does for you — which, given that 4.16 → 4.33 broke
five lines, is the side to err on.

## Getting a toolchain

The only prerequisite is the `lean` binary — there is no Mathlib, no `lakefile`,
and nothing to fetch from a package cache:

```bash
curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
```

The `lean-toolchain` file here then selects v4.33.0 automatically. If you would
rather not install `elan`, the release tarball works standalone:

```bash
curl -sL -o lean.tar.zst \
  https://github.com/leanprover/lean4/releases/download/v4.33.0/lean-4.33.0-linux.tar.zst
zstd -d < lean.tar.zst | tar x
export PATH=$PWD/lean-4.33.0-linux/bin:$PATH
```

**Mathlib is deliberately not used.** Everything is proved from core, which is
most of why this file is worth keeping: it has no dependency that can rot, and
`digitSum`/`numDigits` being built from scratch means nothing about digits is
assumed. The cost is the 60 lines of §0 and the occasional missing lemma —
`pow_lt_pow_left'` is one — which is a good trade for a file this size.
