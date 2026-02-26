**Theorem.**
Let $f, g: \mathbb{C} \to \mathbb{C}$ be complex functions differentiable at a point $z_0$. Suppose $f(z_0) = 0$, $g(z_0) = 0$, and $g'(z_0) \neq 0$. Then:
\[
\lim_{z \to z_0} \frac{f(z)}{g(z)} = \frac{f'(z_0)}{g'(z_0)}.
\]

**Proof.**
Since $f$ and $g$ are differentiable at $z_0$, their derivatives are defined by the limits of their difference quotients:
$$
f'(z_0) = \lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0}
\quad \text{and} \quad
g'(z_0) = \lim_{z \to z_0} \frac{g(z) - g(z_0)}{z - z_0}.
$$

Using the hypotheses $f(z_0) = 0$ and $g(z_0) = 0$, these expressions simplify to:
$$
f'(z_0) = \lim_{z \to z_0} \frac{f(z)}{z - z_0}
\quad \text{and} \quad
g'(z_0) = \lim_{z \to z_0} \frac{g(z)}{z - z_0}.
$$

For any $z \neq z_0$, the term $z - z_0$ is non-zero. Therefore, we can algebraically rewrite the fraction $\frac{f(z)}{g(z)}$ by dividing both the numerator and the denominator by $z - z_0$:
$$
\frac{f(z)}{g(z)} = \frac{\frac{f(z)}{z - z_0}}{\frac{g(z)}{z - z_0}} \quad \text{for } z \neq z_0.
$$

We now take the limit as $z \to z_0$. Since the limit of the denominator exists and is equal to $g'(z_0) \neq 0$, we can apply the quotient rule for limits:
$$
\begin{aligned}
\lim_{z \to z_0} \frac{f(z)}{g(z)} &= \lim_{z \to z_0} \frac{\frac{f(z)}{z - z_0}}{\frac{g(z)}{z - z_0}} \\
&= \frac{\lim_{z \to z_0} \frac{f(z)}{z - z_0}}{\lim_{z \to z_0} \frac{g(z)}{z - z_0}} \\
&= \frac{f'(z_0)}{g'(z_0)}.
\end{aligned}
$$
\qed
