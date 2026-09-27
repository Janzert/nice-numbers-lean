# Nice numbers in Lean 4

Machine-checked proofs of the theorems in
[*Nice Numbers And The Middle Digit Wall*](https://janzert.com/nicenumbers/wall/), a
three-part article series on square–cube pandigitals.

A number `n` is **nice in base `b`** when the base-`b` digits of `n^2` and `n^3` together use
every digit from `0` to `b-1` exactly once. In base 10, `69^2 = 4761` and `69^3 = 328509`; no
other nice number is known in any base. The file works with the general family: `n` is
**`(e1,e2)`-nice** when `n^e1` and `n^e2` share out the digits that way, and `(2,3)` is the
classical case.

Everything here is proved in Lean 4 core — no Mathlib, no `sorry`, no `native_decide` — in a
single file, [`NiceNumbers.lean`](NiceNumbers.lean). Theorems are numbered as in the articles.

## Checking it

```bash
lean NiceNumbers.lean
```

Run it from this directory, so that `elan` finds the [`lean-toolchain`](lean-toolchain) file
and uses Lean v4.33.0. It takes under ten seconds and prints one line per headline result,
from the `#print axioms` block at the end of the file. Each line should list only `propext`,
`Classical.choice` and `Quot.sound` — Lean's three standard axioms — or a subset of them. A
line mentioning `sorryAx` means a proof failed; the errors above it say which.

There is nothing else to fetch: no `lakefile`, no dependencies. To install Lean, see
[Getting Lean](#getting-lean) below.

## What is proved

In the order the articles present them. Every statement holds for **all** bases, and
Theorems 1–10 hold for **all** exponent pairs unless the row says otherwise. The sections of
the file follow the order the proofs were written in, not this order, so each row names its
section.

| | result | main Lean names | file |
|---|---|---|---|
| **1** | **The length obstruction.** If `(e1+e2)` divides `e1·(b-1)`, no `n` gives `n^e1` and `n^e2` a combined `b` digits, so base `b` is dead. Conversely, above an explicit threshold every other base has a candidate, so there the list is complete. (Below the threshold the converse is false: base 3 has no `(2,3)` candidate.) | `no_nice_of_dvd`, `band_nonempty_iff`, `nice_no_solution` | §1, §11 |
| — | **The band's shape.** A given `n` is a candidate in at most one base, so the bands of different bases are disjoint; and within a base the band is a single interval, with both digit lengths constant across it. (It rules nothing out, so the articles give it no number.) | `base_unique`, `bands_disjoint`, `band_convex`, `band_lengths_const` | §3 |
| **2** | **The universal last-digit clash.** If `x^e1` and `x^e2` end in the same digit for *every* `x`, base `b` is dead — and the bases where that happens are exactly the divisors of a single number `N(e1,e2)`. | `no_nice_of_universal_clash`, `clash_iff_dvd_clashMod`, `clash_prime_pow_iff` | §5 |
| **3** | **The parity obstruction.** Every base `b ≡ 3 (mod 4)` is dead, for every exponent pair. | `no_nice_of_mod_four`, `residues_empty_of_mod_four` | §2 |
| **4** | **Which bases the digit sum rules out.** The set of residues a nice number can have modulo `b-1` is empty exactly when `a = 1`, or `a ≥ 3` with `e2-e1` even and `e1 ∤ a-1`, where `a` is the number of times 2 divides `b-1`. Theorem 3 is the case `a = 1`. | `residues_empty_iff`, `residues_nonempty_iff`, `no_nice_of_two_adic` | §7 |
| **5** | **How much a congruence sieve can know.** Modulo `b^j - 1`, a pair of digit lists is worth only `j` block totals. The naive claim that casting out `b-1`s already says everything is **false** (base 4 is a counterexample); under an explicit block-size condition it is true, by an explicit construction. | `valOf_mod_wsum`, `sieve_sound`, `base_four_sieve_is_incomplete`, `sieve_complete` | §6 |
| **6** | **An upper bound on how many nice numbers a base has.** Every nice number lies in the band and passes a test that reads only its low digits, its residue mod `b-1` and its top digits, so counting the survivors bounds the count. At base 10 the bound is exact: the only `(2,3)`-nice number is 69. | `adm_of_pandigital`, `countP_pandigital_le_window`, `admTop_of_pandigital`, `base_ten_nice_iff` | §9 |
| **7** | **The `2/E` construction.** With `gcd(e1·e2, b) = 1` and `E = e1 + e2`, some number's powers leave at most about `b·(1 - 2/E)` digits missing. It never applies to an even base (`no_even_base`). | `greedy_distinct_slots`, `greedy_deficiency_le`, `no_even_base` | §8 |
| **8** | **Infinitely many nice numbers means infinitely many bases with one**, and conversely. | `infinitude_iff`, `nice_base_unique` | §10.4 |
| **9** | **The heuristic count diverges.** Along an explicit infinite family of bases, the expected number of nice numbers exceeds any bound, and none of Theorems 1–4 rules those bases out. | `model_diverges` | §10.0–10.3 |
| **10** | **The conditional.** One named hypothesis, `ModelPositive`, implies infinitely many nice numbers; nothing here proves it. It cannot be weakened to "the heuristic count is large": the `(2,3)` bases `20s+7` have a divergent heuristic count and are all dead by Theorem 3. | `conditional_infinitude`, `ModelPositive`, `divergence_is_not_existence` | §10.5–10.6 |

The comment block at the top of `NiceNumbers.lean` gives each statement precisely, and every
section opens with a prose account of its proof.

## What "machine-checked" covers, and what it does not

Where the articles call a result machine-checked, the statement in this file is verified by
the Lean kernel. Four limits are worth stating plainly:

- **Theorem 2's closed form is not proved.** The file proves that the clashing bases are the
  divisors of `N(e1,e2)` and computes `N` exactly, as a finite gcd. The textbook formula for
  `N` in terms of the Carmichael function needs the structure of the unit group mod `p^a`,
  which core Lean does not have.
- **Theorem 10's hypothesis is not proved.** That is the point of Theorem 10: it isolates the
  one missing input to infinitude.
- **No count is checked.** The exhaustive searches the articles report, and the expected
  counts from the probability model, are computations and estimates, not theorems.
- **The theorems speak about the definitions in the file.** Digits, digit sums, digit counts
  and pandigitality are all defined from scratch by repeated division (§0 and §5), so nothing
  about digits is assumed; but a reader should check that `Pandigital` says what "nice" means.
  `sixtynine_pandigital` and `base_ten_nice_iff` are the quickest sanity checks.

## Guarding against vacuous proofs

An impossibility theorem with contradictory hypotheses proves itself, and a construction
whose conclusion holds of everything proves nothing. So every theorem here comes with
witnesses, checked by the kernel, showing that its hypotheses can hold and that it
**fires** — rules out a base, or builds a number — somewhere that the earlier theorems do not
already cover. The known nice number 69 anchors most of them. Where a theorem has a
threshold or a side condition, a further witness shows it failing just past that condition.

The statements were also **mutation-tested**: weakening a hypothesis or strengthening a
conclusion, then confirming the file no longer compiles. The witnesses caught one real bug:
an early version of Theorem 5 whose hypothesis could never hold, so the theorem type-checked
and said nothing. [NOTES.md](NOTES.md) lists the witnesses and mutations theorem by theorem.

## Getting Lean

```bash
curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
```

installs `elan`, and the `lean-toolchain` file here then selects v4.33.0. Without `elan`, the
release tarball works on its own:

```bash
curl -sL -o lean.tar.zst \
  https://github.com/leanprover/lean4/releases/download/v4.33.0/lean-4.33.0-linux.tar.zst
zstd -d < lean.tar.zst | tar x
export PATH=$PWD/lean-4.33.0-linux/bin:$PATH
```

If `elan`'s default toolchain is the `stable` channel, run `lean` from this directory:
outside it, `elan` does not see `lean-toolchain` and re-resolves `stable` over the network on
every invocation, which adds several seconds that have nothing to do with the proofs.

**Mathlib is deliberately not used.** The file has no dependency that can go out of date,
and building digits from scratch means nothing about them is taken on trust. What Mathlib
would have supplied — mostly counting lemmas — came to about sixty lines here.

## Notes

[NOTES.md](NOTES.md) is the working record of the formalisation: the witnesses and mutation
tests for each theorem, how formalising changed the mathematics (several proofs came out
simpler than the informal ones, and one claim turned out false), what else could be
formalised and at what cost, and the traps met along the way.

## AI involvement

Claude (Anthropic) wrote much of this formalisation — the definitions, the proofs and the
witnesses — as part of the work behind the article series. I directed that work, checked it,
and edited it; every claim here is mine, and I take full responsibility. The proofs themselves
are verified by the Lean 4 kernel, which depends on neither my judgement nor Claude's.

## Author and licence

Brian Haskin (Janzert). Released under the [MIT licence](LICENSE).
