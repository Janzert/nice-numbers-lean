# Formalising the nice-number theorems in Lean 4

**Answer to "can any of the proofs be written in Lean?": yes — Theorems A, B and
G and Proposition D are done, they compile in about a second against Lean core
with no Mathlib, and they are strictly stronger than the exhaustive checks they
replace.** Proposition C′ is a partial fifth: its *soundness* half is proved for
all bases and all `j`, and its completeness half is **disproved** — the
counterexample is in the file.

```bash
lean NiceNumbers.lean      # 1.5 s, 1190 lines, no errors, no sorry
```

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

All of these hold for **all** naturals, and the three gates named above **have been
deleted** from `verify.py` (which is now ~34 s rather than ~44 s). Gate G was
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

## What else is formalisable, and what it would cost

| result | verdict | notes |
|---|---|---|
| ~~**Prop D**~~ — bands for distinct bases are disjoint | **done** (`base_unique`, `bands_disjoint`) | Estimated at ~1 day by the window technique; cost an afternoon by antitonicity of `numDigits` in the base, and came out pair-independent. See above. |
| **Theorem C** — classification of `R_b = ∅`, per pair | **easy per pair, hard in general** | For one pair and one modulus it is a `Decidable` proposition over `ZMod`; `decide` closes it. The general statement needs solvability of `x^{e₁}+x^{e₂} ≡ T (mod p^k)`, i.e. Hensel plus the structure of `(ℤ/p^k)ˣ`. Mathlib-scale, ~1 week per family. |
| ~~**Theorem G**~~ — `q₁(b)=0 ⟺ b ∣ N(e₁,e₂)` | **done** (`no_nice_of_universal_clash`, `clash_iff_dvd_clashMod`, `clash_prime_pow_iff`) | Estimated at ~1 week "needs Carmichael `λ`"; cost an afternoon once `λ` was pushed out of the statement. See above. **What is left is one classical evaluation**: `exponent((ℤ/p^aℤ)ˣ) = λ(p^a)`, i.e. the structure theorem for that group. Mathlib has `Monoid.exponent`; the value at `p^a` would still have to be proved, and only the *closed form* for `N` depends on it. |
| **Theorem F** — the `2/E` greedy bound | **medium-hard, ~2 weeks** | Needs the digit ladder `(r + x·bⁱ)^e ≡ r^e + e·r^{e-1}·x·bⁱ (mod b^{i+1})` (binomial theorem plus a vanishing argument) and a greedy pigeonhole induction. Both are standard; the bookkeeping is not small. |
| ~~**Prop C′**, soundness~~ — the sieve never sees more than `Σ_t b^t S_t` | **done** (`valOf_mod_wsum`, `sieve_sound`) | Estimated inside a "~1 month" for the whole proposition; the soundness half cost an hour, because it is an induction on a list and needs no combinatorics at all. |
| ~~**Prop C′**, completeness~~ — no modulus adds density | **done: it is FALSE** (`base_four_sieve_is_incomplete`) | 256-case kernel `decide` on base 4, lengths `(2,2)`. Both natural mutations of the check are rejected, and `base_four_attained` supplies the three witnesses, so it is neither vacuous nor slack. |
| **Prop C′**, the conditional theorem (REPORT §6.3) | **hard, ~1 month** | Needs the arena construction as an *explicit permutation* of `{0,…,b-1}` — subset-sum contiguity plus list surgery, and core has no `Finset`/`Multiset`. The two arithmetic engines (the block congruence, and the base-`b` no-gap covering) are the easy parts and the first is already done. |
| **Prop C″** — the sharp `c_t ≥ 2` form (REPORT §6.5) | **not yet a proof at all** | Open on paper first. Formalising is not the bottleneck. |
| **T4** — the rigorous upper bound on `#nice(b)` | **not worth it** | An asymptotic statement with error terms. Formalising analytic estimates costs far more than the result is worth here. |
| Part II's yield and cost numbers | **not theorems** | They are heuristic expectations under a random-digit model. Lean has nothing to say about them, and pretending otherwise would be the worst kind of false precision. |
| The exhaustive counts (`(1,3)` has exactly one solution in bases ≤ 44) | **out of the question** | Would need a verified DFS and kernel-level evaluation of ~10¹⁶ candidates. |

**Net effect.** Three of `verify.py`'s gates are now theorems for all inputs
rather than checks over a finite range — and they were the three most general
ones, so they are gone from the script rather than merely superseded. A fourth,
gate G, is narrowed to the single arithmetic identity `N_λ = N_gcd`. A fifth,
gate C′, was **rewritten rather than narrowed**, because formalising its
soundness half exposed that the completeness half it had been sampling is false;
it now checks the conditional theorem, the conjecture, and the counterexamples.
Two caveats worth keeping in view: Theorem A's *converse* (every base outside the
dead class really does have candidates) is **not** proved and stays an empirical
check, and neither is the closed form for `N`, for want of `λ(p^a)`.

**The "no cheap piece left on the shelf" claim in the previous revision was
wrong, and wrong in an instructive way.** C′ was costed at ~1 month as a single
lump. Split into soundness and completeness it was an hour and an afternoon,
because *the two halves need completely different machinery* — soundness is one
induction over a list, completeness is a construction in a combinatorial category
core Lean has no vocabulary for. The lesson is to cost the halves, not the
proposition: an estimate for a biconditional is an estimate for its hardest
direction, and quoting it for the pair hides whatever is cheap. What is left in
the table now really is a project apiece.

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
