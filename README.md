# RMS formal proofs

Lean 4 formalizations of selected answers to questions from the *Revue de la filière Mathématiques*.

The canonical problem list is available at <https://lucpommeret.com/assets/Qsansreponse260405.pdf>.

## Intermediate book

An automatically generated intermediate edition containing every answer whose
current Lean artifact has passed the repository CI is available as
[`publication/main.pdf`](publication/main.pdf). Each section states its informal
audit verdict, the exact scope currently formalized, and links to the immutable
Lean source and online type-check. This edition is updated as the proof campaign
progresses.

## Verification

Every file under `lean/RMS/` is checked by GitHub Actions with the Lean and mathlib versions pinned in `lean/lean-toolchain` and `lean/lakefile.toml`.

Current formalizations:

- `Q565*.lean` — Bell-number asymptotics with the first relative correction;
- `Q587.lean` — interpolated Taylor expansions;
- `Q604.lean` — explicit polynomial Bézout coefficients;
- `Q668.lean` — verified structural results for cyclic absolute differences (partial coverage);
- `Q701.lean` — extreme points of an anchored Hölder ball;
- `Q728.lean` — complete classification of the stick-splitting game;
- `Q730*.lean` — the singular-value/eigenvalue block-form classification;
- `Q756*.lean` — smooth flat non-polynomial solutions of the dilation equation;
- `Q759.lean` — two sequences converging in the smooth topology;
- `Q764.lean` — mathematical core of the line and finite-metric center algorithms (complexity layer pending);
- `Q781.lean` — translation separation in compact topological groups;
- `Q803.lean` — exact finite-stage characterization of achievement sets with empty interior;
- `Q831.lean` — universal formulas for elementary symmetric polynomials of powers.

These files were generated with Aristotle and are independently type-checked by the repository CI. Kernel acceptance certifies the formal statements, while correspondence with the original informal questions is audited separately.
