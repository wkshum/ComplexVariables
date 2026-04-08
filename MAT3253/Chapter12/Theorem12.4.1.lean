/- This project was edited by [Aristotle](https://aristotle.harmonic.fun).

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib
open Filter Topology Set
set_option maxHeartbeats 8000000
/-!
# Equivalence of Locally Uniform Convergence and Compact Convergence
We prove that for a sequence of complex-valued functions on a nonempty open connected domain D ⊆ ℂ,
the following are equivalent:
1. **Locally uniform convergence**: For every z₀ ∈ D, there exists a neighborhood U of z₀
   such that fₖ → f uniformly on U.
2. **Compact convergence**: For every compact set K ⊆ D, fₖ → f uniformly on K.
-/
/-- Locally uniform convergence: at every point of D, there is a neighborhood
    on which the sequence converges uniformly. -/
def LocallyUniformConvergence (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∀ z₀ ∈ D, ∃ U ∈ 𝓝 z₀, TendstoUniformlyOn F f atTop U
/-- Compact convergence: the sequence converges uniformly on every compact subset of D. -/
def CompactConvergence (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∀ K ⊆ D, IsCompact K → TendstoUniformlyOn F f atTop K
/-
Locally uniform convergence implies compact convergence for sequences of
    complex functions on a nonempty open connected domain.
-/
theorem locallyUniform_implies_compact
    (D : Set ℂ) (hD_open : IsOpen D) (hD_nonempty : D.Nonempty) (hD_conn : IsConnected D)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hloc : LocallyUniformConvergence F f D) :
    CompactConvergence F f D := by
  intro K hK_sub hK_compact
  have h_neighborhoods : ∀ z ∈ K, ∃ U ∈ 𝓝 z, TendstoUniformlyOn F f atTop U := by
    exact fun z hz => hloc z ( hK_sub hz )
  generalize_proofs at *; (
  choose! U hU using h_neighborhoods;
  -- Since $K$ is compact, we can find a finite subcover of $K$ by the neighborhoods $U_z$.
  obtain ⟨z_fin, hz_fin⟩ : ∃ z_fin : Finset ℂ, (∀ z ∈ z_fin, z ∈ K) ∧ K ⊆ ⋃ z ∈ z_fin, U z := by
    have := hK_compact.elim_nhds_subcover U fun z hz => hU z hz |>.1; aesop;
  generalize_proofs at *; (
  simp_all +decide [ Metric.tendstoUniformlyOn_iff ];
  intro ε hε; choose! a ha using fun z hz => hU z ( hz_fin.1 z hz ) |>.2 ε hε; use Finset.sup z_fin a; intro n hn x hx; rcases Set.mem_iUnion₂.1 ( hz_fin.2 hx ) with ⟨ z, hz, hxz ⟩ ; exact ha z hz n ( le_trans ( Finset.le_sup hz ) hn ) x hxz;))
/-
Compact convergence implies locally uniform convergence for sequences of
    complex functions on a nonempty open connected domain.
-/
theorem compact_implies_locallyUniform
    (D : Set ℂ) (hD_open : IsOpen D) (hD_nonempty : D.Nonempty) (hD_conn : IsConnected D)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hcpt : CompactConvergence F f D) :
    LocallyUniformConvergence F f D := by
  -- Given that F converges compactly to f on D, we need to show that F converges locally uniformly to f on D.
  intro z₀ hz₀
  obtain ⟨r, hr_pos, hr⟩ : ∃ r > 0, (Metric.closedBall z₀ r) ⊆ D := by
    exact Metric.nhds_basis_closedBall.mem_iff.mp ( hD_open.mem_nhds hz₀ );
  exact ⟨ Metric.closedBall z₀ r, Metric.closedBall_mem_nhds _ hr_pos, hcpt _ hr ( ProperSpace.isCompact_closedBall _ _ ) ⟩
/-- **Main theorem**: Locally uniform convergence and compact convergence are equivalent
    for sequences of complex functions on a nonempty open connected domain D ⊆ ℂ. -/
theorem locallyUniform_iff_compact
    (D : Set ℂ) (hD_open : IsOpen D) (hD_nonempty : D.Nonempty) (hD_conn : IsConnected D)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) :
    LocallyUniformConvergence F f D ↔ CompactConvergence F f D :=
  ⟨locallyUniform_implies_compact D hD_open hD_nonempty hD_conn F f,
   compact_implies_locallyUniform D hD_open hD_nonempty hD_conn F f⟩
