# Formalising the nice-number theorems in Lean 4

**Answer to "can any of the proofs be written in Lean?": yes — Theorems A and B
are done, they compile in under a second against Lean core with no Mathlib, and
they are strictly stronger than the exhaustive checks they replace.**

```bash
lean NiceNumbers.lean      # <1 s, 356 lines, no errors, no sorry
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
| `no_nice_of_dvd` | `(e₁+e₂) ∣ e₁*(b-1)` ⟹ `numDigits b (n^e₁) + numDigits b (n^e₂) ≠ b` | `verify.py` gate A, which checked `e₁ ≤ 8, e₂ ≤ 9, b < 120` |
| `nice_no_solution` | base `b ≡ 1 (mod 5)` has no square/cube candidate | the `(2,3)` instance |
| `one_three_no_solution` | base `b ≡ 1 (mod 4)` has no `(1,3)` candidate | the `(1,3)` instance |
| `two_four_no_solution` | base `b ≡ 1 (mod 3)` has no `(2,4)` candidate | the `gcd > 1` instance |
| `no_nice_of_mod_four` | for **every** pair `e₁,e₂ ≥ 1`, base `b ≡ 3 (mod 4)` fails the digit-sum identity | `verify.py` gate B, which checked `e₁ ≤ 8, e₂ ≤ 9, b < 400` |

Both now hold for **all** naturals, so those two exhaustive gates can be deleted.

`numDigits` and `digitSum` are defined from scratch by repeated division
(60 lines, including `bounds_of_numDigits`: `numDigits b x = k+1 ↔ b^k ≤ x < b^(k+1)`,
and `digitSum_mod`: casting out `b-1`s). Nothing about digits is assumed.

## Non-vacuity — the check that matters most

An impossibility theorem with contradictory hypotheses proves itself. §3 of the
file rules that out, kernel-checked:

* `length_identity_holds : numDigits 10 (69^2) + numDigits 10 (69^3) = 10`
* `digitsum_identity_holds : 2 * (digitSum 10 (69^2) + digitSum 10 (69^3)) = 10 * (10-1)`

i.e. 69 in base 10 — the only known nice number — satisfies both hypothesis
families. Then two theorems shown *firing*: `base_eleven_dead` (Theorem A at
`b = 11`) and `base_seven_dead` (Theorem B at `b = 7`, where Theorem A says
nothing because `7 ≢ 1 mod 5`), plus `base_seven_dead'` at exponents `(3,8)` to
show B really is pair-independent.

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

## What else is formalisable, and what it would cost

| result | verdict | notes |
|---|---|---|
| **Prop D** — bands for distinct bases are disjoint | **easy, ~1 day** | Same window technique as A. Best next target: it is the last *fully general* claim in the report still resting on a finite check (`b < 200`, six pairs). |
| **Theorem C** — classification of `R_b = ∅`, per pair | **easy per pair, hard in general** | For one pair and one modulus it is a `Decidable` proposition over `ZMod`; `decide` closes it. The general statement needs solvability of `x^{e₁}+x^{e₂} ≡ T (mod p^k)`, i.e. Hensel plus the structure of `(ℤ/p^k)ˣ`. Mathlib-scale, ~1 week per family. |
| **Theorem G** — `q₁(b)=0 ⟺ b ∣ N(e₁,e₂)` | **medium, ~1 week** | Needs Carmichael `λ`. Mathlib has `Monoid.exponent (ZMod n)ˣ` but the explicit value at `p^a` would likely have to be proved. The *sufficiency* half — `b ∣ N` ⟹ base dead — is easy and is the half that does work. |
| **Theorem F** — the `2/E` greedy bound | **medium-hard, ~2 weeks** | Needs the digit ladder `(r + x·bⁱ)^e ≡ r^e + e·r^{e-1}·x·bⁱ (mod b^{i+1})` (binomial theorem plus a vanishing argument) and a greedy pigeonhole induction. Both are standard; the bookkeeping is not small. |
| **Prop C′** — completeness of the congruence sieve | **hard, ~1 month** | The real content is combinatorial: which block-sum vectors of an ordered partition of `{0,…,b-1}` occur. Multiset/`List.Perm` machinery, genuinely Mathlib-scale. |
| **T4** — the rigorous upper bound on `#nice(b)` | **not worth it** | An asymptotic statement with error terms. Formalising analytic estimates costs far more than the result is worth here. |
| Part II's yield and cost numbers | **not theorems** | They are heuristic expectations under a random-digit model. Lean has nothing to say about them, and pretending otherwise would be the worst kind of false precision. |
| The exhaustive counts (`(1,3)` has exactly one solution in bases ≤ 44) | **out of the question** | Would need a verified DFS and kernel-level evaluation of ~10¹⁶ candidates. |

**Net effect.** Of the nine gates in `verify.py`, two are now theorems for all
inputs rather than checks over a finite range — and they were the two most
general ones. Prop D is a cheap third. Everything past that is a real
formalisation project rather than a weekend.

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
