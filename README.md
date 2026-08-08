# RMS formal proofs

Lean 4 formalizations of selected answers to questions from the *Revue de la filière Mathématiques*.

The canonical problem list is available at <https://lucpommeret.com/assets/Qsansreponse260405.pdf>.

## Verification

Every file under `lean/RMS/` is checked by GitHub Actions with the Lean and mathlib versions pinned in `lean/lean-toolchain` and `lean/lakefile.toml`.

Current formalizations:

- `Q587.lean` — interpolated Taylor expansions;
- `Q604.lean` — explicit polynomial Bézout coefficients;
- `Q668.lean` — asymptotic classification of cyclic absolute differences;
- `Q701.lean` — extreme points of an anchored Hölder ball.

These files were generated with Aristotle and are independently type-checked by the repository CI. Kernel acceptance certifies the formal statements, while correspondence with the original informal questions is audited separately.
