# FlowCE Steps: design

2026-10-14 · branch `steps` · baseline: upstream v1.9 (`c32720d`)

## Goal

For a Calculus 2 student on a TI-84 Plus CE: after FlowCE answers a derivative or an integral,
show textbook-style worked steps, detailed enough to apply the same method on paper to her own
problems. Every step names the rule and, where a choice is made, the choice ("Let u = 3x,
du = 3 dx", "u = x, dv = eˣ dx"). A wrong step is never shown.

Must have: derivatives and integrals (u-substitution, integration by parts, partial fractions,
trig integrals and trig substitution). Optional: limits, only if flash space is left.

## What the user sees

- Typing a derivative (`diff(f,x)`, the d/dx template, higher derivatives) or an integral
  (indefinite or definite) works as today.
- **`2nd` `F4` opens the Steps screen** when the result selected in the history, or the one just
  shown large, comes from a derivative or an integral. The bar's F4 tab says "steps" for the
  2nd layer then. Otherwise `2nd` `F4` keeps its current menu (polynomials). `F4` alone still
  cycles the forms, unchanged.
- The Steps screen (full screen, Focus look, Paper and Night themes):
  - top: the problem in 2D;
  - each step: a bold rule label ("Product rule", "u-substitution", "Integration by parts",
    "Partial fractions", "Simplify"...), an optional choice line ("Let u = 3x, du = 3 dx"), then
    the expression in 2D;
  - last: the answer as FlowCE shows it (with + C for antiderivatives); a definite integral
    ends with "Evaluate from a to b" and the bounds substituted;
  - `↑`/`↓` scroll, `clear` returns to the calculation.
- When the tracer cannot explain a problem, or a check fails: "No steps for this one. The
  answer is still correct." No partial or guessed steps.

## Architecture

New code is isolated in two files; giac's engine is not modified.

| Unit | File | Job |
| --- | --- | --- |
| Step list | `src/steps.h` | `struct step { label, choice, expr text }`, a capped vector of steps, `steps_build(input) -> ok/none/aborted` |
| Derivative tracer | `src/steps.cc` | Walks f outside-in; one step per rule application |
| Integral tracer | `src/steps.cc` | Tries the techniques in textbook order; first one that verifies wins |
| Steps screen | `src/focus_steps.cc` | Draws and scrolls the list with the existing 2D layout (`ui_math_fit`, `ui_math_draw`) |
| Hooks | `src/console.cc`, `src/focus.cc` | `2nd` `F4` dispatch and bar label |

Giac is used as a toolbox only: `derive`, `subst`, `partfrac`, `simplify`/`normal`, `lvar`,
`integrate` (for verification and for sub-integrals the tracer reduced to table form).

### Derivative tracer

Rules, each one step: sum/difference, constant multiple, power (incl. x^n, n rational/negative,
sqrt), product, quotient, chain (any composite; the step names the outer and inner function),
exponential (eˣ, aˣ), logarithmic (ln, log_b), trig (sin, cos, tan, sec, csc, cot), inverse trig
(asin, acos, atan), and logarithmic differentiation for a variable base and exponent (x^x,
x^cot(x)): "Take ln of both sides", differentiate, solve for y'. Trivial derivatives (constants, d/dx x = 1) are folded into the step that
uses them. Higher derivatives repeat the trace on the previous result. Last step: "Simplify",
only when it changes the expression.

### Integral tracer

Tried in order; the first technique whose result verifies is shown:

1. Basic rules and table: linearity (sum, constant multiple), power rule, 1/x, eˣ, aˣ, sin, cos,
   sec², csc², sec·tan, csc·cot, 1/(1+x²), 1/√(1−x²); a linear inner argument (ax+b) counts as
   table form with the 1/a factor stated.
2. u-substitution: candidates u = the inner arguments of composite functions and denominators
   (from `lvar`), kept when f/u' is expressible in u alone; steps: "Let u = …, du = … dx",
   the integral in u, integrate, substitute back.
3. Integration by parts: u chosen by LIATE, dv the rest; steps: "u = …, dv = … dx",
   "du = … dx, v = …", uv − ∫v du, then the new integral traced recursively (repeated parts,
   e.g. ∫x²eˣ); the cyclic case (∫eˣ sin x) solved by "the integral appears again".
4. Partial fractions: rational f; polynomial division first when improper; the decomposition
   from `partfrac`, then each term by the table.
5. Trig integrals and trig substitution: powers of sin/cos (odd power: split off one factor and
   use sin² + cos² = 1; even: half-angle), powers of tan/sec; √(a²−x²) → x = a sin θ,
   √(a²+x²) → x = a tan θ, √(x²−a²) → x = a sec θ, then back-substitution with the triangle.

Recursion depth and the number of steps are capped (RAM: about 150 KB free on the CE).

### Verification

- Each step's expression is checked against the previous one: `simplify(a − b) == 0` (for
  integrals, up to an added constant: the derivative of the difference simplifies to 0).
- The final antiderivative is differentiated and compared with the integrand.
- The final step must equal FlowCE's own answer (up to a constant for antiderivatives).
- Any failed check: the whole trace is discarded and "No steps for this one" is shown.

### Errors and limits

- Steps are computed only when `2nd` `F4` is pressed, never during a normal calculation, so
  answers do not get slower and the existing answer pipeline is unchanged.
- `clear` or `on` during a slow trace stops it ("Stopped"); running out of memory stops it with
  "Out of memory" (FlowCE's `oom_hit` / `ctrl_c` handling, as for the F4 forms).

## Flash space

- Measured baseline: `_DEMO.bin` 2,794,188 B; 23,857 B left under the 2,818,045 B cap.
- First, drop giac's Python-syntax translator (`python2xcas`, 28.4 KB; the switch already exists
  for the units edition) behind a new flag; normal math input is unaffected. Room: about 52 KB.
- Estimate for the new code: derivatives about 10 KB, integrals 20 to 35 KB, screen about 4 KB.
- If more room is needed, next candidates (each measured and agreed with the user before removal):
  the program editor, Laplace transforms. Kept regardless: series/sums, polar/parametric,
  graphing, solve, limits, simple differential equations.
- The build already refuses an app over the cap; the size is recorded after each part.

## Order of work

1. Python-syntax switch off; full emulator suite (715 problems) shows no regression.
2. Step list + Steps screen + `2nd` `F4` hook (with a stub trace), emulator screenshots.
3. Derivative tracer.
4. Integral tracer: table → u-sub → parts → partial fractions → trig.
5. Limits (substitution, factor/cancel, conjugate, L'Hôpital) only if space remains.

## Testing

- Host (PC build, `tools/hostgiac`): steps.cc compiled in; a `-S` driver option prints the steps
  of each problem. A cases file of derivatives and integrals with expected step labels,
  including: d/dx x²sin(3x), sin(x²), eˣ/x, ln(cos x), x^x (logarithmic
  differentiation); ∫x eˣ, ∫x² sin x, ∫eˣ sin x, ∫2x cos(x²), ∫1/(x²−1),
  ∫(x+4)/(x²+4x+8), ∫sin³x, ∫tan⁴x, ∫√(9−x²), ∫1/(x²√(x²+4)).
- Emulator: Steps screen screenshots for a set of problems; the 715-problem suite after every
  part with no new differences, timeouts or hangs versus the v1.9 baseline.
- Real calculator: only after the emulator passes; `FlowCE.b84` installed with the web
  installer.

## Out of scope

- Steps for anything other than derivatives, integrals and (optionally) limits.
- Changing giac's own results or the F4 forms.
- French text for the Steps screen (the English build only).
