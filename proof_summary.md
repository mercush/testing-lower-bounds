# Proof of monotoneOn for DivFunction

## Lemma Statement
`lemma monotoneOn (f : DivFunction) : MonotoneOn f (Ici 1)`

This states that any `DivFunction` `f` is monotone increasing on the interval `[1, ∞)`.

## Key Properties Used

1. **DivFunction properties:**
   - `f : ℝ≥0∞ → ℝ≥0∞`
   - `f(1) = 0`
   - `f` is convex on `ℝ≥0`
   - `f` is continuous

2. **Key insight:** Since `f` is convex with `f(1) = 0` and has a minimum at 1 (from `rightDeriv_one_nonneg` and `leftDeriv_one_nonpos`), it must be increasing on `[1, ∞)`.

## Proof Strategy

For `1 ≤ x ≤ y`, we want to show `f(x) ≤ f(y)`.

1. **Base case:** If `x = 1`, then `f(x) = f(1) = 0 ≤ f(y)`.

2. **Main case:** For `1 < x ≤ y`, we express `x` as a convex combination of `1` and `y`:
   ```
   x = ((y-x)/(y-1)) • 1 + ((x-1)/(y-1)) • y
   ```
   where the coefficients sum to 1.

3. **Apply convexity:** By the convexity of `f`:
   ```
   f(x) ≤ ((y-x)/(y-1)) • f(1) + ((x-1)/(y-1)) • f(y)
        = 0 + ((x-1)/(y-1)) • f(y)
        = ((x-1)/(y-1)) • f(y)
   ```

4. **Final step:** Since `x ≤ y` implies `(x-1)/(y-1) ≤ 1`, we have:
   ```
   f(x) ≤ ((x-1)/(y-1)) • f(y) ≤ f(y)
   ```

## Technical Details

The proof handles several edge cases:
- When `x = y` (trivial)
- When `y = 1` (impossible given `x ≤ y` and `1 ≤ x`)
- Ensuring all values are finite (since `x, y ≥ 1`)

The convex combination coefficients are constructed as `ℝ≥0` values and the arithmetic is done in `ℝ≥0∞`.