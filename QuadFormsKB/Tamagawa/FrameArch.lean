/-
# The archimedean density of forms by forms and the archimedean fibration for frames

**Layer:** real numbers (Gamma function, real powers); the closed form `archVolSO` of $\mathrm{vol}(SO_N(\mathbb R))$.

**Defines**
* `epsNR N r` $= \varepsilon_{N,r}$: $\tfrac12$ if $r = N$, else $1$ (Siegel 1935 [unverified]);
* `archDensityForm N r D_Q D_T` (**the archimedean density** $\beta_\sigma(Q, T)$ in the repository's coefficient coordinates):
  $$\beta_\infty(Q,T) = 2^{-r(r-1)/2}\prod_{i=0}^{r-1}\frac{\pi^{(N-i)/2}}{\Gamma(\frac{N-i}2)}\;D_T^{(N-r-1)/2}\,D_Q^{-r/2},$$
  $D_Q = \det(H_Q/2)$, $D_T = \det(H_T/2)$. For $r = 1$ it is `archRepDensity` (`archDensityForm_one`). The factor $2^{-r(r-1)/2}$ converts
  Siegel's Gram coordinates $a_{ij}$ to the coefficients $c_{ij} = 2a_{ij}$ ($i<j$) of `repCountForm`.

**Proves**
* `archVolSO_blockForm` (**the archimedean fibration for frames**): $\mathrm{vol}(SO_N, D_TD')\,(2^rD_T)^{n'} = \mathrm{vol}(SO_{n'}, D')\,\beta_\infty$,
  $N = r + n'$; for $r = 1$ this is `archVolSO_succ`;
* `archDensityForm_self`: $\varepsilon_{N,N}\,\beta_\infty(Q, Q) = \mathrm{vol}(SO_N, D_Q)$ (used for $T = Q$).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.MassInduction

open scoped Real

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa

/-- **Siegel's factor** $\varepsilon_{N,r}$: $\tfrac12$ if $r = N$, else $1$. -/
def epsNR (N r : ℕ) : ℝ := if r = N then 1 / 2 else 1

/-- **Siegel's factor in codimension one** $\varepsilon'_{N,r}$: $\tfrac12$ if $r = N - 1$, else $1$. Siegel's $\varepsilon$ is $\tfrac12$ for
$r = N - 1$ as well as for $r = N$ (Siegel 1935, Hauptsatz [unverified]). For $r = N$ the repository applies it at every place
(`epsNR`); for $r = N - 1$ it is a single global factor (it comes from $\mathrm{Mass}$ of a rank-one lattice being $\tfrac12$ while its
Tamagawa measure is $1$, i.e. $\tau(SO_1) = 1$), since a factor $\tfrac12$ at every prime would make the product $0$. -/
def epsCodimOne (N r : ℕ) : ℝ := if r + 1 = N then 1 / 2 else 1

/-- **The archimedean density of $T$ by $Q$** at a real place, in coefficient coordinates (Siegel 1935, §1 [unverified]):
$\beta_\infty = 2^{-r(r-1)/2}\prod_{i<r}\pi^{(N-i)/2}/\Gamma(\frac{N-i}2)\cdot D_T^{(N-r-1)/2}D_Q^{-r/2}$. -/
@[kb "siegel1935" "§1 (archimedean density of forms) [unverified]"]
def archDensityForm (N r : ℕ) (DQ DT : ℝ) : ℝ :=
  ((2 : ℝ) ^ (r * (r - 1) / 2))⁻¹ *
    (∏ i ∈ Finset.range r, Real.pi ^ (((N : ℝ) - i) / 2) / Real.Gamma (((N : ℝ) - i) / 2)) *
    DT ^ (((N : ℝ) - r - 1) / 2) * DQ ^ (-(r : ℝ) / 2)

/-- Triangular numbers split additively: $\binom{r+n'}{2} = \binom{n'}2 + rn' + \binom r2$. -/
theorem tri_add (r n' : ℕ) :
    (r + n') * (r + n' - 1) / 2 = n' * (n' - 1) / 2 + r * n' + r * (r - 1) / 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : r + 1 + n' = (r + n') + 1 := by omega
    rw [h1, nat_tri_succ, nat_tri_succ, ih]
    have : (r + 1) * n' = r * n' + n' := by ring
    omega

/-- Reflection of the Gamma product. -/
theorem prod_arch_reflect (N r : ℕ) (hr : r ≤ N) :
    ∏ i ∈ Finset.range r, Real.pi ^ (((N : ℝ) - i) / 2) / Real.Gamma (((N : ℝ) - i) / 2) =
      ∏ j ∈ Finset.range r, Real.pi ^ ((((N - r + j : ℕ) : ℝ) + 1) / 2) /
        Real.Gamma ((((N - r + j : ℕ) : ℝ) + 1) / 2) := by
  rw [← Finset.prod_range_reflect (fun j : ℕ => Real.pi ^ ((((N - r + j : ℕ) : ℝ) + 1) / 2) /
        Real.Gamma ((((N - r + j : ℕ) : ℝ) + 1) / 2)) r]
  apply Finset.prod_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have : (((N - r + (r - 1 - i) : ℕ) : ℝ) + 1) = (N : ℝ) - i := by
    have e : N - r + (r - 1 - i) + 1 = N - i := by omega
    have e2 : (((N - r + (r - 1 - i) : ℕ) : ℝ) + 1) = ((N - i : ℕ) : ℝ) := by exact_mod_cast e
    rw [e2, Nat.cast_sub (by omega)]
  rw [this]

/-- $\beta_\infty(Q, \langle a\rangle) = $ `archRepDensity`. -/
theorem archDensityForm_one (N : ℕ) (DQ a : ℝ) : archDensityForm N 1 DQ a = archRepDensity N a DQ := by
  unfold archDensityForm archRepDensity
  simp only [Finset.prod_range_one, Nat.cast_one, Nat.sub_self,Nat.zero_div, pow_zero,
    inv_one, one_mul, Nat.cast_zero, sub_zero]
  congr 2
  · ring_nf
  · ring_nf

/-- **The archimedean fibration for frames** ($D_T, D' > 0$; $N = r + n'$):
$$\mathrm{vol}(SO_N, D_TD')\cdot(2^rD_T)^{n'} = \mathrm{vol}(SO_{n'}, D')\cdot\beta_\infty(Q, T),$$
the factor $(2^rD_T)^{n'} = |\det H_T|^{n'}$ being the Jacobian of the cross coefficients $B(X_i, y_j)$ (for $r = 1$:
`archVolSO_succ`). -/
@[kb "siegel1935" "§1 (archimedean densities) [unverified]"]
theorem archVolSO_blockForm (r n' : ℕ) {DT D' : ℝ} (hDT : 0 < DT) (hD' : 0 < D') :
    archVolSO (r + n') (DT * D') * (2 ^ r * DT) ^ n' = archVolSO n' D' * archDensityForm (r + n') r (DT * D') DT := by
  unfold archVolSO archDensityForm
  have hP := prod_arch_reflect (r + n') r (by omega)
  rw [show r + n' - r = n' by omega] at hP
  have hPN : ∏ j ∈ Finset.range (r + n'), Real.pi ^ (((j : ℝ) + 1) / 2) / Real.Gamma (((j : ℝ) + 1) / 2) =
      (∏ j ∈ Finset.range n', Real.pi ^ (((j : ℝ) + 1) / 2) / Real.Gamma (((j : ℝ) + 1) / 2)) *
      ∏ i ∈ Finset.range r, Real.pi ^ (((r + n' : ℕ) - (i : ℝ)) / 2) /
        Real.Gamma (((r + n' : ℕ) - (i : ℝ)) / 2) := by
    rw [add_comm r n', Finset.prod_range_add, add_comm n' r, hP]
  have hd : (DT * D') ^ (-(((r + n' : ℕ) : ℝ) + 1) / 2) * DT ^ n' =
      D' ^ (-((n' : ℝ) + 1) / 2) * DT ^ ((((r + n' : ℕ) : ℝ) - r - 1) / 2) * (DT * D') ^ (-(r : ℝ) / 2) := by
    rw [Real.mul_rpow hDT.le hD'.le, Real.mul_rpow hDT.le hD'.le, ← Real.rpow_natCast DT n']
    have h1 : DT ^ (-(((r + n' : ℕ) : ℝ) + 1) / 2) * DT ^ (n' : ℝ) =
        DT ^ ((((r + n' : ℕ) : ℝ) - r - 1) / 2) * DT ^ (-(r : ℝ) / 2) := by
      rw [← Real.rpow_add hDT, ← Real.rpow_add hDT]; congr 1; push_cast; ring
    have h2 : D' ^ (-(((r + n' : ℕ) : ℝ) + 1) / 2) =
        D' ^ (-((n' : ℝ) + 1) / 2) * D' ^ (-(r : ℝ) / 2) := by
      rw [← Real.rpow_add hD']; congr 1; push_cast; ring
    calc _ = (DT ^ (-(((r + n' : ℕ) : ℝ) + 1) / 2) * DT ^ (n' : ℝ)) * D' ^ (-(((r + n' : ℕ) : ℝ) + 1) / 2) := by ring
      _ = _ := by rw [h1, h2]; ring
  rw [hPN, tri_add, mul_pow, ← pow_mul, pow_add, pow_add]
  have hB : (2 : ℝ) ^ (r * n') ≠ 0 := by positivity
  have hA : (2 : ℝ) ^ (n' * (n' - 1) / 2) ≠ 0 := by positivity
  have hC : (2 : ℝ) ^ (r * (r - 1) / 2) ≠ 0 := by positivity
  calc _ = 1 / 2 * ((2 : ℝ) ^ (n' * (n' - 1) / 2))⁻¹ * ((2 : ℝ) ^ (r * (r - 1) / 2))⁻¹ *
        (∏ j ∈ Finset.range n', Real.pi ^ (((j : ℝ) + 1) / 2) / Real.Gamma (((j : ℝ) + 1) / 2)) *
        (∏ i ∈ Finset.range r, Real.pi ^ (((r + n' : ℕ) - (i : ℝ)) / 2) /
          Real.Gamma (((r + n' : ℕ) - (i : ℝ)) / 2)) *
        ((DT * D') ^ (-(((r + n' : ℕ) : ℝ) + 1) / 2) * DT ^ n') := by field_simp
    _ = _ := by rw [hd]; ring

/-- $\varepsilon_{N,N}\,\beta_\infty(Q,Q) = \mathrm{vol}(SO_N, D_Q)$ for $N \ge 1$, $D_Q > 0$. -/
theorem archDensityForm_self (N : ℕ) (hN : 1 ≤ N) {DQ : ℝ} (hDQ : 0 < DQ) :
    epsNR N N * archDensityForm N N DQ DQ = archVolSO N DQ := by
  have hP := prod_arch_reflect N N le_rfl
  rw [Nat.sub_self] at hP
  simp only [zero_add] at hP
  unfold archVolSO archDensityForm
  rw [hP]
  have e : DQ ^ (((N : ℝ) - N - 1) / 2) * DQ ^ (-(N : ℝ) / 2) = DQ ^ (-((N : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add hDQ]; congr 1; ring
  simp only [epsNR, ite_true]
  rw [← e]; ring

end QuadFormsKB.Tamagawa.Frames
