/-
# Cassels, Appendix B, Example 5: Schur's determination of the sign of the quadratic Gauss sum

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), Example 5, p. 390 (Schur 1921).

**Setting.** $F$ is the Fourier transform `dftF` on $\mathbb C^n$, $(F\Phi)_k = n^{-1/2}\sum_j \Phi_j\, e(jk/n)$, indexed
by residues $j, k \in \mathbb Z/n$ (Cassels' $a_0,\dots,a_{n-1}$; the indices are already 0-based). Here $F^4 = 1$
(`dftF_pow_four`), so $\mathbb C^n$ is the direct sum of the eigenspaces of the eigenvalues $i^u$, $u = 0,1,2,3$, with
dimensions $m_u$ = `dftMult n u`.

**Formalized (all proved, no assumed input).**
* (i) $\sum_u m_u = n$ (`dftMult_sum`), the trace, the trace of the square and the determinant of $F$ in terms of $m_u$
  (generic lemmas `trace_eq_eigMult`, `trace_sq_eq_eigMult`, `det_eq_eigMult` for any $f$ with $f^4 = 1$).
* (ii) $m_0 + m_2$ and $m_1 + m_3$ (`dftMult_parity`).
* (iii) $\operatorname{tr}F = (\sqrt p)^{-1}\tau(\chi,p)$ (`trace_dftLin_prime`) and
  $(m_0-m_2)^2 + (m_1-m_3)^2 = 1$ (`dftMult_sq_sum_prime`; *erratum* in the printed indices).
* (iv) $\det F = i^{(n-1)^2 + n(n-1)/2}$ (`dftLin_det`), via the Vandermonde determinant (`det_dftLin`,
  `vandermonde_prod`), and $\sum_u u\,m_u \equiv (n-1)^2 + n(n-1)/2 \pmod 4$ (`dftMult_det`).
* (v) $\tau(\chi,p) = \sqrt p$ or $i\sqrt p$ (`gauss_sum_value`, `gauss_sum_tau`): the sign of the quadratic Gauss sum.
* (vi) $\sum_{j \bmod n} e(j^2/n) = \sqrt n$, $i\sqrt n$ for $n \equiv 1, 3 \pmod 4$ (`schur_gauss_sum_odd`),
  $0$ for $n \equiv 2$ (`schur_gauss_sum_two`).

**Not fully formalized.** (vi) for $n \equiv 0 \pmod 4$: only $\sum_j e(j^2/n) = \pm(1+i)\sqrt n$
(`schur_gauss_sum_zero`). The eigenvalue-multiplicity method with the determinant leaves two possibilities with the same
determinant and the same squared trace; the sign needs one more input.

**Conventions.** $e(x) = e^{2\pi i x}$; `ZMod.stdAddChar (j * k)` is $e(jk/n)$; $\sqrt n > 0$ is `Real.sqrt n`.
Dimension $n \ge 1$ (`NeZero n`); Cassels assumes $n > 1$, which is not needed.
-/
import QuadFormsKB.Literature.Cassels.AppB.Examples

open Complex Module Finset

namespace QuadFormsKB.Cassels


section Generic

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Helper: the multiplicity $m_u$ of the eigenvalue $i^u$ ($u \in \{0,1,2,3\}$, $i = \sqrt{-1}$) of an endomorphism $f$ of a finite-dimensional complex vector space, defined as the dimension of the eigenspace $\ker(f - i^u)$. Arguments: `f` the endomorphism, `u` the exponent (an element of `Fin 4`, so $u = 0,\dots,3$). -/
noncomputable def eigMult (f : End ℂ V) (u : Fin 4) : ℕ :=
  finrank ℂ (End.eigenspace f (Complex.I ^ (u : ℕ)))

/-- Helper: $u \mapsto i^u$ is injective on `Fin 4` (the four powers $1, i, -1, -i$ are distinct). -/
theorem I_pow_injective : Function.Injective (fun u : Fin 4 => (Complex.I ^ (u : ℕ))) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [Complex.ext_iff] at h ⊢ <;> norm_num at h

/-- Helper: if $f^4 = 1$ then the space is the internal direct sum of the four eigenspaces $\ker(f - i^u)$, $u = 0,\dots,3$ (Mathlib: $X^4 - 1$ is squarefree, so $f$ is semisimple, and every eigenvalue is a fourth root of unity). Arguments: `f` the endomorphism, `hf : f ^ 4 = 1`. -/
theorem eigen_isInternal (f : End ℂ V) (hf : f ^ 4 = 1) :
    DirectSum.IsInternal (fun u : Fin 4 => End.eigenspace f (Complex.I ^ (u : ℕ))) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨(End.eigenspaces_iSupIndep f).comp I_pow_injective, ?_⟩
  have hsq : Squarefree (Polynomial.X ^ 4 - Polynomial.C (1 : ℂ) : Polynomial ℂ) :=
    (Polynomial.separable_X_pow_sub_C (1 : ℂ) (by norm_num) one_ne_zero).squarefree
  have hss : f.IsSemisimple := by
    apply End.isSemisimple_of_squarefree_aeval_eq_zero hsq
    simp [hf]
  have htop := hss.iSup_eigenspace_eq_top
  rw [eq_top_iff, ← htop]
  refine iSup_le (fun μ => ?_)
  by_cases hμ : End.eigenspace f μ = ⊥
  · rw [hμ]; exact bot_le
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
    have h4 : μ ^ 4 = 1 := by
      have hx' : f x = μ • x := End.mem_eigenspace_iff.mp hx
      have : (f ^ 4) x = μ ^ 4 • x := by
        have key : ∀ k : ℕ, (f ^ k) x = μ ^ k • x := by
          intro k
          induction k with
          | zero => simp
          | succ k ih => rw [pow_succ, Module.End.mul_apply, hx', map_smul, ih, smul_smul, pow_succ]; ring_nf
        exact key 4
      rw [hf] at this
      have h1 : (1 - μ ^ 4) • x = 0 := by rw [sub_smul, one_smul, ← this]; simp
      rcases smul_eq_zero.mp h1 with h2 | h2
      · linear_combination -h2
      · exact absurd h2 hx0
    have : ∃ u : Fin 4, μ = Complex.I ^ (u : ℕ) := by
      have h0 : (μ - 1) * (μ + 1) * (μ - Complex.I) * (μ + Complex.I) = 0 := by
        linear_combination h4 + (-(μ ^ 2 - 1)) * Complex.I_sq
      rcases mul_eq_zero.mp h0 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact ⟨0, by simp; linear_combination h⟩
          · exact ⟨2, by simp; linear_combination h⟩
        · exact ⟨1, by simp; linear_combination h⟩
      · exact ⟨3, by simp [pow_succ]; linear_combination h⟩
    obtain ⟨u, rfl⟩ := this
    exact le_iSup (fun u : Fin 4 => End.eigenspace f (Complex.I ^ (u : ℕ))) u

/-- Helper: if $f^4 = 1$, there is a basis (indexed by a finite type `ι`) of eigenvectors in which $f$ is diagonal, with diagonal entries `d a`; the diagonal entries are $i^u$ repeated $m_u$ times, so sums and products over `d` are sums and products over $u$ weighted by $m_u$, and the basis has $\sum_u m_u$ elements. Arguments: `f` the endomorphism, `hf : f ^ 4 = 1`. -/
theorem eigen_diag (f : End ℂ V) (hf : f ^ 4 = 1) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι ℂ V) (d : ι → ℂ),
      (LinearMap.toMatrix b b f = Matrix.diagonal d) ∧
      (∀ g : ℂ → ℂ, ∑ a, g (d a) = ∑ u : Fin 4, (eigMult f u : ℂ) * g (Complex.I ^ (u : ℕ))) ∧
      (∏ a, d a = ∏ u : Fin 4, (Complex.I ^ (u : ℕ)) ^ eigMult f u) ∧
      Fintype.card ι = ∑ u : Fin 4, eigMult f u := by
  classical
  have h := eigen_isInternal f hf
  let bs := fun u : Fin 4 => Module.finBasis ℂ (End.eigenspace f (Complex.I ^ (u : ℕ)))
  let b := h.collectedBasis bs
  refine ⟨_, inferInstance, inferInstance, b, fun a => Complex.I ^ (a.1 : ℕ), ?_, ?_, ?_, ?_⟩
  · ext i j
    rw [LinearMap.toMatrix_apply]
    have : f (b j) = (Complex.I ^ (j.1 : ℕ)) • b j := by
      rw [DirectSum.IsInternal.collectedBasis_coe]
      have := (bs j.1 j.2).2
      exact End.mem_eigenspace_iff.mp this
    rw [this, map_smul, Matrix.diagonal_apply]
    simp [Finsupp.single_apply, eq_comm]
    by_cases hij : i = j
    · subst hij; rfl
    · simp [hij]
  · intro g
    rw [Fintype.sum_sigma]
    simp [eigMult]
  · rw [Fintype.prod_sigma]
    simp [eigMult]
  · simp [eigMult, Fintype.card_sigma]

/-- Helper (generic form of Cassels, Appendix B, Example 5 (i), p. 390): if $f^4 = 1$ then $m_0 + m_1 + m_2 + m_3 = \dim V$. Arguments: `f` the endomorphism, `hf : f ^ 4 = 1`. -/
theorem eigMult_sum (f : End ℂ V) (hf : f ^ 4 = 1) : ∑ u : Fin 4, eigMult f u = finrank ℂ V := by
  classical
  obtain ⟨ι, _, _, b, d, -, -, -, hc⟩ := eigen_diag f hf
  rw [← hc, Module.finrank_eq_card_basis b]

/-- Helper: if $f^4 = 1$ then $\operatorname{tr} f = \sum_u m_u\, i^u$. Arguments: `f`, `hf : f ^ 4 = 1`. -/
theorem trace_eq_eigMult (f : End ℂ V) (hf : f ^ 4 = 1) :
    LinearMap.trace ℂ V f = ∑ u : Fin 4, (eigMult f u : ℂ) * Complex.I ^ (u : ℕ) := by
  classical
  obtain ⟨ι, _, _, b, d, hm, hs, -, -⟩ := eigen_diag f hf
  rw [LinearMap.trace_eq_matrix_trace ℂ b, hm, Matrix.trace_diagonal]
  simpa using hs id

/-- Helper: if $f^4 = 1$ then $\operatorname{tr} f^2 = \sum_u m_u\, (i^u)^2$. Arguments: `f`, `hf : f ^ 4 = 1`. -/
theorem trace_sq_eq_eigMult (f : End ℂ V) (hf : f ^ 4 = 1) :
    LinearMap.trace ℂ V (f * f) = ∑ u : Fin 4, (eigMult f u : ℂ) * (Complex.I ^ (u : ℕ)) ^ 2 := by
  classical
  obtain ⟨ι, _, _, b, d, hm, hs, -, -⟩ := eigen_diag f hf
  rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.toMatrix_mul, hm, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  have := hs (fun z => z ^ 2)
  simp only [sq] at this ⊢
  simpa using this

/-- Helper: if $f^4 = 1$ then $\det f = \prod_u (i^u)^{m_u}$. Arguments: `f`, `hf : f ^ 4 = 1`. -/
theorem det_eq_eigMult (f : End ℂ V) (hf : f ^ 4 = 1) :
    LinearMap.det f = ∏ u : Fin 4, (Complex.I ^ (u : ℕ)) ^ eigMult f u := by
  classical
  obtain ⟨ι, _, _, b, d, hm, -, hp, -⟩ := eigen_diag f hf
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, hp]

end Generic

section Fourier

/-- Helper: the Fourier transform `dftF n` as a $\mathbb C$-linear endomorphism of $\mathbb C^n$ (functions $\mathbb Z/n \to \mathbb C$). Argument: `n` the length. -/
noncomputable def dftLin (n : ℕ) [NeZero n] : End ℂ (ZMod n → ℂ) where
  toFun := dftF n
  map_add' Φ Ψ := by
    funext k
    simp only [dftF, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c Φ := by
    simpa using dftF_smul n c Φ

/-- Helper: `dftLin n` acts as `dftF n`. Arguments: `n` the length, `Φ` the function. -/
theorem dftLin_apply (n : ℕ) [NeZero n] (Φ : ZMod n → ℂ) : dftLin n Φ = dftF n Φ := rfl

/-- Helper: the reflection $\Phi \mapsto (k \mapsto \Phi(-k))$ as a linear endomorphism. Argument: `n` the modulus. -/
def reflLin (n : ℕ) : End ℂ (ZMod n → ℂ) where
  toFun Φ := fun k => Φ (-k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Helper: $F \circ F$ is the reflection (`dftF_dftF` as an identity of linear maps). Argument: `n` the length. -/
theorem dftLin_mul_self (n : ℕ) [NeZero n] : dftLin n * dftLin n = reflLin n := by
  exact LinearMap.ext fun Φ => dftF_dftF n Φ

/-- Helper: $F^4 = I$ as an identity of linear maps (`dftF_pow_four`). Argument: `n` the length. -/
theorem dftLin_pow_four (n : ℕ) [NeZero n] : dftLin n ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, dftLin_mul_self]
  ext Φ k
  simp [reflLin]

/-- Helper: $\operatorname{tr} F = \frac1{\sqrt n}\sum_{k \bmod n} e(k^2/n)$, since the diagonal entry of $F$ in the position $k$ is $\frac1{\sqrt n}e(k\cdot k/n)$. Argument: `n` the length. -/
theorem trace_dftLin (n : ℕ) [NeZero n] :
    LinearMap.trace ℂ _ (dftLin n) = ((Real.sqrt n : ℝ) : ℂ)⁻¹ * ∑ k : ZMod n, (ZMod.stdAddChar (k * k) : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (ZMod n)), Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [dftLin_apply, dftF, Pi.single_apply]

/-- Helper: the trace of the reflection $k \mapsto -k$ is the number of residues $k$ with $-k = k$. Argument: `n` the length. -/
theorem trace_reflLin (n : ℕ) [NeZero n] :
    LinearMap.trace ℂ _ (reflLin n) = ((Finset.univ.filter (fun k : ZMod n => -k = k)).card : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (ZMod n)), Matrix.trace, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [reflLin, Pi.single_apply, eq_comm]

/-- Helper: for odd $n = 2m+1$ exactly one residue ($0$) satisfies $-k = k$. Arguments: `n` the modulus, `m` with `hn : n = 2 * m + 1`. -/
theorem card_self_neg_odd (n m : ℕ) [NeZero n] (hn : n = 2 * m + 1) :
    (Finset.univ.filter (fun k : ZMod n => -k = k)).card = 1 := by
  subst hn
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    have h2 : (2 : ZMod (2 * m + 1)) * k = 0 := by linear_combination -h
    have hn : ((2 * m + 1 : ℕ) : ZMod (2 * m + 1)) = 0 := ZMod.natCast_self _
    push_cast at hn
    linear_combination ((m : ZMod (2 * m + 1)) + 1) * h2 - k * hn
  · rintro rfl; simp

/-- Helper: for even $n = 2m$ exactly two residues ($0$ and $m$) satisfy $-k = k$. Arguments: `n` the modulus, `m` with `hn : n = 2 * m`. -/
theorem card_self_neg_even (n m : ℕ) [NeZero n] (hn : n = 2 * m) :
    (Finset.univ.filter (fun k : ZMod n => -k = k)).card = 2 := by
  subst hn
  have hm : 0 < m := by
    have := NeZero.ne (2 * m); omega
  have hm0 : ((m : ℕ) : ZMod (2 * m)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd hm h
    omega
  rw [Finset.card_eq_two]
  refine ⟨0, (m : ZMod (2 * m)), hm0.symm, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have h2 : ((2 * k.val : ℕ) : ZMod (2 * m)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination -h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hlt := ZMod.val_lt k
    obtain ⟨c, hc⟩ := h2
    have hc' : k.val = m * c := by nlinarith
    have : c = 0 ∨ c = 1 := by
      by_contra hcc
      push Not at hcc
      have : 2 ≤ c := by omega
      nlinarith
    rcases this with rfl | rfl
    · left
      have : k.val = 0 := by simpa using hc'
      exact (ZMod.val_eq_zero k).mp this
    · right
      rw [← ZMod.natCast_zmod_val k, show k.val = m by simpa using hc']
  · rintro (rfl | rfl)
    · simp
    · have : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
      push_cast at this
      linear_combination (-1 : ZMod (2 * m)) * this

/-- The multiplicity $m_u$ of the eigenvalue $i^u$ of the Fourier transform $F$ on $\mathbb C^n$ ($u = 0,1,2,3$), i.e. the dimension of $\ker(F - i^u)$. Arguments: `n` the length, `u` the exponent in `Fin 4`. -/
noncomputable def dftMult (n : ℕ) [NeZero n] (u : Fin 4) : ℕ := eigMult (dftLin n) u

/-- **Cassels, Appendix B, Example 5 (i), p. 390 (multiplicities):** the eigenvalues of $F$ are among $i^u$ ($u = 0,1,2,3$; `dftF_eigenvalue`), $\mathbb C^n$ is the direct sum of the eigenspaces (`eigen_isInternal`), and the multiplicities $m_u$ = `dftMult n u` satisfy $m_0 + m_1 + m_2 + m_3 = n$. Argument: `n` the length. -/
@[kb "cassels1978" "App. B, Ex. 5 (i), p. 390 (multiplicities m_u, m_0+m_1+m_2+m_3 = n)"]
theorem dftMult_sum (n : ℕ) [NeZero n] : ∑ u : Fin 4, dftMult n u = n := by
  show ∑ u : Fin 4, eigMult (dftLin n) u = n
  rw [eigMult_sum _ (dftLin_pow_four n)]
  simp

/-- Helper: $\operatorname{tr} F = (m_0 - m_2) + i\,(m_1 - m_3)$, which is $\frac1{\sqrt n}\sum_k e(k^2/n)$. Argument: `n` the length. -/
theorem dftMult_trace (n : ℕ) [NeZero n] :
    ((dftMult n 0 : ℤ) - dftMult n 2 : ℂ) + ((dftMult n 1 : ℤ) - dftMult n 3 : ℂ) * Complex.I =
      ((Real.sqrt n : ℝ) : ℂ)⁻¹ * ∑ k : ZMod n, (ZMod.stdAddChar (k * k) : ℂ) := by
  rw [← trace_dftLin, trace_eq_eigMult _ (dftLin_pow_four n), Fin.sum_univ_four]
  simp [dftMult, pow_succ]
  ring

/-- Helper: $\operatorname{tr}F^2 = m_0 - m_1 + m_2 - m_3$ equals the number of residues $k$ with $-k = k$ (the trace of the reflection). Argument: `n` the length. -/
theorem dftMult_trace_sq (n : ℕ) [NeZero n] :
    ((dftMult n 0 : ℤ) - dftMult n 1 + dftMult n 2 - dftMult n 3 : ℤ) =
      ((Finset.univ.filter (fun k : ZMod n => -k = k)).card : ℤ) := by
  have h := trace_sq_eq_eigMult _ (dftLin_pow_four n)
  rw [dftLin_mul_self, trace_reflLin, Fin.sum_univ_four] at h
  simp [dftMult, pow_succ] at h ⊢
  have h' : ((eigMult (dftLin n) 0 : ℤ) - eigMult (dftLin n) 1 + eigMult (dftLin n) 2 - eigMult (dftLin n) 3 : ℂ) =
      ((Finset.univ.filter (fun k : ZMod n => -k = k)).card : ℤ) := by
    push_cast
    rw [h]; ring
  exact_mod_cast h'

/-- **Cassels, Appendix B, Example 5 (ii), second part (p. 390):** $F^2$ is the reflection, whose trace is $1$ for $n$ odd and $2$ for $n$ even, and $\operatorname{tr}F^2 = (m_0+m_2) - (m_1+m_3)$ with $\sum m_u = n$. Hence, for $n$ odd, $m_0 + m_2 = (n+1)/2$ and $m_1 + m_3 = (n-1)/2$ (stated as `2 * (m_0 + m_2) = n + 1`, `2 * (m_1 + m_3) + 1 = n`), and for $n$ even, $m_0 + m_2 = n/2 + 1$ and $m_1 + m_3 = n/2 - 1$. Argument: `n` the length. -/
@[kb "cassels1978" "App. B, Ex. 5 (ii), p. 390 (m_0+m_2 and m_1+m_3)"]
theorem dftMult_parity (n : ℕ) [NeZero n] :
    (n % 2 = 1 → 2 * (dftMult n 0 + dftMult n 2) = n + 1 ∧ 2 * (dftMult n 1 + dftMult n 3) + 1 = n) ∧
    (n % 2 = 0 → dftMult n 0 + dftMult n 2 = n / 2 + 1 ∧ dftMult n 1 + dftMult n 3 + 1 = n / 2) := by
  have hs := dftMult_sum n
  have ht := dftMult_trace_sq n
  rw [Fin.sum_univ_four] at hs
  constructor
  · intro h
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    rw [card_self_neg_odd n m hm] at ht
    omega
  · intro h
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    rw [card_self_neg_even n m hm] at ht
    omega

/-- Helper: $\big((m_0-m_2)^2 + (m_1-m_3)^2\big)\,n = \big|\sum_{k \bmod n}e(k^2/n)\big|^2$ (the absolute value squared of $\sqrt n\operatorname{tr}F$). Argument: `n` the length. -/
theorem dftMult_gauss_norm (n : ℕ) [NeZero n] :
    (((dftMult n 0 : ℤ) - dftMult n 2) ^ 2 + ((dftMult n 1 : ℤ) - dftMult n 3) ^ 2 : ℤ) * n =
      Complex.normSq (∑ k : ZMod n, (ZMod.stdAddChar (k * k) : ℂ)) := by
  have h := congrArg Complex.normSq (dftMult_trace n)
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hr : Complex.normSq (((Real.sqrt n : ℝ) : ℂ)⁻¹) = (n : ℝ)⁻¹ := by
    rw [map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hn.le]
  rw [map_mul, hr] at h
  have hl : Complex.normSq (((dftMult n 0 : ℤ) - dftMult n 2 : ℂ) + ((dftMult n 1 : ℤ) - dftMult n 3 : ℂ) * Complex.I)
      = (((dftMult n 0 : ℤ) - dftMult n 2) ^ 2 + ((dftMult n 1 : ℤ) - dftMult n 3) ^ 2 : ℤ) := by
    rw [Complex.normSq_apply]
    simp
    ring
  rw [hl] at h
  have : (((((dftMult n 0 : ℤ) - dftMult n 2) ^ 2 + ((dftMult n 1 : ℤ) - dftMult n 3) ^ 2 : ℤ) * n : ℤ) : ℝ) =
      Complex.normSq (∑ k : ZMod n, (ZMod.stdAddChar (k * k) : ℂ)) := by
    push_cast
    push_cast at h
    rw [h]; field_simp
  exact_mod_cast this

/-- Helper: the equivalence `Fin n ≃ ZMod n` sends `a` to the residue of the natural number `a`. Arguments: `n` the modulus, `a` the element. -/
theorem finEquiv_eq (n : ℕ) [NeZero n] (a : Fin n) : ZMod.finEquiv n a = ((a : ℕ) : ZMod n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  simp only [ZMod.finEquiv]
  exact (Fin.cast_val_eq_self a).symm

/-- Helper: $\det F = (\sqrt n)^{-n}\prod_{0\le i<j<n}(\zeta^j - \zeta^i)$ with $\zeta = e(1/n)$, the Vandermonde determinant of the matrix $(\zeta^{ij})$. Argument: `n` the length. -/
theorem det_dftLin (n : ℕ) [NeZero n] :
    LinearMap.det (dftLin n) = (((Real.sqrt n : ℝ) : ℂ)⁻¹) ^ n *
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        (Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) / n) - Complex.exp (2 * Real.pi * Complex.I * (i : ℕ) / n)) := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (ZMod n))]
  have hM : LinearMap.toMatrix (Pi.basisFun ℂ (ZMod n)) (Pi.basisFun ℂ (ZMod n)) (dftLin n) =
      ((Real.sqrt n : ℝ) : ℂ)⁻¹ • Matrix.of (fun i j : ZMod n => (ZMod.stdAddChar (j * i) : ℂ)) := by
    ext i j
    simp [dftLin_apply, dftF, Pi.single_apply]
  rw [hM, Matrix.det_smul, ZMod.card]
  congr 1
  rw [← Matrix.det_vandermonde, ← Matrix.det_submatrix_equiv_self (ZMod.finEquiv n).toEquiv]
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, RingEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, finEquiv_eq]
  have h := ZMod.stdAddChar_coe (N := n) (((b : ℕ) * (a : ℕ) : ℕ) : ℤ)
  push_cast at h
  rw [h, ← Complex.exp_nat_mul]
  congr 1
  ring

end Fourier



/-- Helper: exchange of summation for the pairs $i<j$ in `Fin n`: $\sum_{i}\sum_{j>i} g(j) = \sum_j j\,g(j)$. Arguments: `n` the length, `g` the summand. -/
theorem sum_Ioi_comm (n : ℕ) (g : ℕ → ℕ) :
    ∑ i : Fin n, ∑ j ∈ Ioi i, g j = ∑ j : Fin n, (j : ℕ) * g j := by
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Iio j)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    simp
  · intro x y
    simp

/-- Helper: $2\sum_{i<n} i = n(n-1)$. Argument: `n`. -/
theorem sum_fin_id (n : ℕ) : (∑ i : Fin n, (i : ℕ)) * 2 = n * (n - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
  exact Finset.sum_range_id_mul_two n

/-- Helper: the number of pairs $i<j$ in `Fin n` is $n(n-1)/2$ (stated doubled). Argument: `n`. -/
theorem card_pairs (n : ℕ) : (∑ i : Fin n, (Ioi i).card) * 2 = n * (n - 1) := by
  have : ∑ i : Fin n, (Ioi i).card = ∑ j : Fin n, (j : ℕ) := by
    have h := sum_Ioi_comm n (fun _ => 1)
    simpa using h
  rw [this, sum_fin_id]

/-- Helper: $\sum_{i<j}(i+j) = n(n-1)^2/2$ over pairs in `Fin n` (stated doubled). Argument: `n`. -/
theorem sum_pairs (n : ℕ) : (∑ i : Fin n, ∑ j ∈ Ioi i, ((i : ℕ) + j)) * 2 = n * (n - 1) ^ 2 := by
  have h1 : ∑ i : Fin n, ∑ j ∈ Ioi i, ((i : ℕ) + (j : ℕ)) =
      ∑ i : Fin n, ((i : ℕ) * (n - 1 - i) + (i : ℕ) * i) := by
    simp_rw [Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [mul_comm]
    · have := sum_Ioi_comm n (fun j => j)
      simpa using this
  have h2 : ∑ i : Fin n, ((i : ℕ) * (n - 1 - i) + (i : ℕ) * i) = ∑ i : Fin n, (i : ℕ) * (n - 1) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← mul_add]
    congr 1
    have := i.2
    omega
  rw [h1, h2, ← Finset.sum_mul, mul_assoc, mul_comm (n - 1) 2, ← mul_assoc, sum_fin_id]
  ring

/-- Helper: for $0\le i<j<n$, $e(j/n)-e(i/n) = e\big(\tfrac{i+j}{2n}\big)\cdot 2\sin\big(\tfrac{\pi(j-i)}{n}\big)\cdot i$ (written with $\exp(2\pi i\,\cdot)$). Arguments: `n` the modulus, `i`, `j` the indices. -/
theorem exp_sub_exp (n : ℕ) [NeZero n] (i j : Fin n) :
    Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) / n) - Complex.exp (2 * Real.pi * Complex.I * (i : ℕ) / n) =
      Complex.exp ((Real.pi * ((i : ℕ) + (j : ℕ)) / n : ℝ) * Complex.I) *
        (((2 * Real.sin (Real.pi * ((j : ℕ) - (i : ℕ)) / n) : ℝ) : ℂ) * Complex.I) := by
  have hd : ∀ z : ℂ, Complex.exp (z * Complex.I) - Complex.exp (-z * Complex.I) =
      2 * Complex.sin z * Complex.I := by
    intro z
    rw [Complex.sin]
    linear_combination (Complex.exp (z * Complex.I) - Complex.exp (-z * Complex.I)) * Complex.I_sq
  have h1 := hd ((Real.pi * ((j : ℕ) - (i : ℕ)) / n : ℝ) : ℂ)
  push_cast at h1 ⊢
  have e1 : Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) / n) =
      Complex.exp (Real.pi * ((i : ℕ) + (j : ℕ)) / n * Complex.I) *
        Complex.exp (Real.pi * ((j : ℕ) - (i : ℕ)) / n * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (2 * Real.pi * Complex.I * (i : ℕ) / n) =
      Complex.exp (Real.pi * ((i : ℕ) + (j : ℕ)) / n * Complex.I) *
        Complex.exp (-(Real.pi * ((j : ℕ) - (i : ℕ)) / n) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1, e2, ← mul_sub, h1]

/-- Helper: if $i^k$ is a positive real number then $4 \mid k$. Arguments: `k` the exponent, `ρ` the positive real number, `hρ` its positivity, `h` the equation $i^k = \rho$. -/
theorem I_pow_eq_pos (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (h : Complex.I ^ k = (ρ : ℂ)) : k % 4 = 0 := by
  have : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
  have h4 : Complex.I ^ (4 * (k / 4)) = 1 := by rw [pow_mul]; simp
  rw [this, pow_add, h4, one_mul] at h
  have hk : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : k % 4
  · rfl
  · exfalso; have := congrArg Complex.re h; simp at this; linarith
  · exfalso; have := congrArg Complex.re h; simp [pow_two] at this; linarith
  · exfalso; have := congrArg Complex.re h; simp [pow_succ] at this; linarith

/-- Helper: the Vandermonde product $\prod_{i<j}(\zeta^j-\zeta^i)$, $\zeta = e(1/n)$, equals a positive real number times $i^{(n-1)^2 + n(n-1)/2}$. (The phase $e\big(\sum_{i<j}(i+j)/2n\big) = e((n-1)^2/4) = i^{(n-1)^2}$ and the factor $i$ from each of the $n(n-1)/2$ pairs; the sines are positive since $0<\pi(j-i)/n<\pi$.) Argument: `n` the length. -/
theorem vandermonde_prod (n : ℕ) [NeZero n] :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∏ i : Fin n, ∏ j ∈ Ioi i,
        (Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) / n) - Complex.exp (2 * Real.pi * Complex.I * (i : ℕ) / n))
        = (ρ : ℂ) * Complex.I ^ ((n - 1) ^ 2 + n * (n - 1) / 2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hpos : ∀ i : Fin n, ∀ j ∈ Ioi i, 0 < 2 * Real.sin (Real.pi * ((j : ℕ) - (i : ℕ)) / n) := by
    intro i j hj
    have hij : (i : ℕ) < j := Fin.lt_def.mp (Finset.mem_Ioi.mp hj)
    have hjn : (j : ℕ) < n := j.2
    have h1 : (0 : ℝ) < ((j : ℕ) : ℝ) - (i : ℕ) := by
      have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
      linarith
    have h2 : ((j : ℕ) : ℝ) - (i : ℕ) < n := by
      have : ((j : ℕ) : ℝ) < n := by exact_mod_cast hjn
      have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have : 0 < Real.sin (Real.pi * ((j : ℕ) - (i : ℕ)) / n) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · rw [div_lt_iff₀ hn]
        nlinarith [Real.pi_pos]
    linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ∏ i : Fin n, ∏ j ∈ Ioi i, 2 * Real.sin (Real.pi * ((j : ℕ) - (i : ℕ)) / n) :=
    ⟨_, rfl⟩
  refine ⟨ρ, hρ ▸ Finset.prod_pos (fun i _ => Finset.prod_pos (fun j hj => hpos i j hj)), ?_⟩
  have hcast : (ρ : ℂ) = ∏ i : Fin n, ∏ j ∈ Ioi i,
      (((2 * Real.sin (Real.pi * ((j : ℕ) - (i : ℕ)) / n) : ℝ)) : ℂ) := by
    rw [hρ, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun _ _ => Complex.ofReal_prod _ _
  rw [hcast]
  simp_rw [exp_sub_exp]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
  have hC : ∑ i : Fin n, (Ioi i).card = n * (n - 1) / 2 := by have := card_pairs n; omega
  have hA : ∏ i : Fin n, ∏ j ∈ Ioi i,
      Complex.exp (((Real.pi * ((i : ℕ) + (j : ℕ)) / n : ℝ) : ℂ) * Complex.I) =
      Complex.I ^ ((n - 1) ^ 2) := by
    simp_rw [← Complex.exp_sum]
    have hI : ∀ k : ℕ, Complex.I ^ k = Complex.exp ((k : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I)) := by
      intro k; rw [Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
    rw [hI]
    congr 1
    have hS := sum_pairs n
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (NeZero.pos n)]; simp
    have hSr : ((∑ i : Fin n, ∑ j ∈ Ioi i, ((i : ℕ) + (j : ℕ)) : ℕ) : ℝ) * 2 = n * ((n : ℝ) - 1) ^ 2 := by
      rw [← hn1]; exact_mod_cast hS
    have hR : ∑ i : Fin n, ∑ j ∈ Ioi i, (Real.pi * ((i : ℕ) + (j : ℕ)) / n : ℝ) =
        Real.pi / n * ((∑ i : Fin n, ∑ j ∈ Ioi i, ((i : ℕ) + (j : ℕ)) : ℕ) : ℝ) := by
      push_cast
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp_rw [← Finset.sum_mul, ← Complex.ofReal_sum]
    rw [hR]
    have hnr : (n : ℝ) ≠ 0 := hn.ne'
    have : Real.pi / n * ((∑ i : Fin n, ∑ j ∈ Ioi i, ((i : ℕ) + (j : ℕ)) : ℕ) : ℝ) =
        ((n - 1) ^ 2 : ℕ) * (Real.pi / 2) := by
      generalize ((∑ i : Fin n, ∑ j ∈ Ioi i, ((i : ℕ) + (j : ℕ)) : ℕ) : ℝ) = Sr at hSr ⊢
      have hS' : Sr = n * ((n : ℝ) - 1) ^ 2 / 2 := by linarith
      rw [hS', Nat.cast_pow, hn1]
      field_simp
    rw [this]
    push_cast
    ring
  rw [hA, hC, pow_add]
  ring


/-- **Cassels, Appendix B, Example 5 (iv), p. 390 (the determinant of $F$ modulo 4):** $\det F = \prod_u (i^u)^{m_u} = i^{\sum_u u\,m_u}$ is also $(\sqrt n)^{-n}$ times a Vandermonde determinant, a positive real number times $i^{N}$, $N = (n-1)^2 + n(n-1)/2$; $\det F$ being a fourth root of unity forces the positive number to be $1$, hence $\sum_u u\,m_u \equiv N \pmod 4$. Argument: `n` the length. -/
@[kb "cassels1978" "App. B, Ex. 5 (iv), p. 390 (Σ u m_u ≡ (n-1)^2 + n(n-1)/2 mod 4)"]
theorem dftMult_det (n : ℕ) [NeZero n] :
    (∑ u : Fin 4, (u : ℕ) * dftMult n u) % 4 = ((n - 1) ^ 2 + n * (n - 1) / 2) % 4 := by
  have h1 := det_eq_eigMult _ (dftLin_pow_four n)
  rw [det_dftLin] at h1
  obtain ⟨ρ, hρ, hprod⟩ := vandermonde_prod n
  rw [hprod] at h1
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hc : (0 : ℝ) < (Real.sqrt n)⁻¹ ^ n * ρ := by positivity
  set N := (n - 1) ^ 2 + n * (n - 1) / 2 with hN
  set s := ∑ u : Fin 4, (u : ℕ) * dftMult n u with hs
  have h2 : ∏ u : Fin 4, (Complex.I ^ (u : ℕ)) ^ eigMult (dftLin n) u = Complex.I ^ s := by
    rw [hs, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl (fun u _ => ?_)
    rw [← pow_mul]; rfl
  rw [h2] at h1
  have h3 : Complex.I ^ (s + 3 * N) = (((Real.sqrt n)⁻¹ ^ n * ρ : ℝ) : ℂ) := by
    have h4 : Complex.I ^ (4 * N) = 1 := by rw [pow_mul]; simp
    calc Complex.I ^ (s + 3 * N) = Complex.I ^ s * Complex.I ^ (3 * N) := pow_add _ _ _
      _ = (((Real.sqrt n : ℝ) : ℂ)⁻¹ ^ n * ((ρ : ℂ) * Complex.I ^ N)) * Complex.I ^ (3 * N) := by rw [h1]
      _ = ((Real.sqrt n : ℝ) : ℂ)⁻¹ ^ n * ρ * Complex.I ^ (N + 3 * N) := by rw [pow_add]; ring
      _ = _ := by
        rw [show N + 3 * N = 4 * N by ring, h4]; push_cast; ring
  have := I_pow_eq_pos _ _ hc h3
  omega

/-- Helper: `quadDir p` is a quadratic character (values $0, \pm1$). Argument: `p` the prime. -/
theorem quadDir_isQuadratic (p : ℕ) [Fact p.Prime] : (quadDir p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

/-- Helper: `quadDir p` is not the trivial character for an odd prime. Arguments: `p` the prime, `hp2 : p ≠ 2`. -/
theorem quadDir_ne_one (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : quadDir p ≠ 1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hF
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  intro h
  have h1 := congrArg (fun χ : MulChar (ZMod p) ℂ => χ a) h
  simp only [MulChar.one_apply (isUnit_iff_ne_zero.mpr ha0)] at h1
  have : quadDir p a = -1 := by
    simp [quadDir, quadraticChar_neg_one_iff_not_isSquare.mpr ha]
  rw [this] at h1
  norm_num at h1

/-- Helper: $\chi(-1) = 1$ if $p \equiv 1 \pmod 4$ and $-1$ otherwise (odd prime $p$), for $\chi$ = `quadDir p`. Arguments: `p` the prime, `hp2 : p ≠ 2`. -/
theorem quadDir_neg_one (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    quadDir p (-1) = if p % 4 = 1 then 1 else -1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  by_cases h : p % 4 = 1
  · have hsq : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
    simp [h, quadDir, (quadraticChar_one_iff_isSquare hne).mpr hsq]
  · have hsq : ¬ IsSquare (-1 : ZMod p) := fun hh => by
      have := ZMod.exists_sq_eq_neg_one_iff.mp hh
      omega
    simp [h, quadDir, quadraticChar_neg_one_iff_not_isSquare.mpr hsq]

/-- Helper: $\big(\sum_x e(x^2/p)\big)^2 = \pm p$, with sign $+$ iff $p \equiv 1 \pmod 4$ (`sum_sq_eq_gauss` and `gauss_sq`). Arguments: `p` the prime, `hp2 : p ≠ 2`. -/
theorem gauss_sum_sq_prime (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (∑ x : ZMod p, (ZMod.stdAddChar (x * x) : ℂ)) ^ 2 = (if p % 4 = 1 then 1 else -1) * p := by
  rw [sum_sq_eq_gauss p hp2, gauss_sq p (quadDir p) (quadDir_ne_one p hp2) (quadDir_isQuadratic p),
    quadDir_neg_one p hp2]

/-- Helper: $(\operatorname{tr}F)^2 = \pm1$, with sign $+$ iff $p \equiv 1 \pmod 4$, for a prime $p \ne 2$. Arguments: `p` the prime, `hp2 : p ≠ 2`. -/
theorem trace_sq_prime (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ((((Real.sqrt p : ℝ) : ℂ)⁻¹) * ∑ x : ZMod p, (ZMod.stdAddChar (x * x) : ℂ)) ^ 2 =
      if p % 4 = 1 then 1 else -1 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hsq2 : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = p := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg p)]; simp
  rw [mul_pow, gauss_sum_sq_prime p hp2, inv_pow, sq, hsq2]
  field_simp

/-- Helper (arithmetic of the case $p \equiv 1 \pmod 4$): from the multiplicity relations, the determinant relation modulo 4, and $a^2 - b^2 = 1$, $ab = 0$ for $a = m_0 - m_2$, $b = m_1-m_3$, conclude $a = 1$, $b = 0$. Arguments: `p` a natural number $\equiv 1 \bmod 4$ (the odd prime or the odd modulus), `m0 … m3` the multiplicities, the hypotheses as named. -/
theorem arith_one (p m0 m1 m2 m3 : ℕ) (hp : p % 4 = 1) (h2 : 2 * (m0 + m2) = p + 1)
    (h3 : 2 * (m1 + m3) + 1 = p) (hdet : (m1 + 2 * m2 + 3 * m3) % 4 = ((p - 1) ^ 2 + p * (p - 1) / 2) % 4)
    (hq : ((m0 : ℤ) - m2) * ((m0 : ℤ) - m2) - ((m1 : ℤ) - m3) * ((m1 : ℤ) - m3) = 1)
    (hq2 : ((m0 : ℤ) - m2) * ((m1 : ℤ) - m3) = 0) : (m0 : ℤ) - m2 = 1 ∧ (m1 : ℤ) - m3 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
  have hN : ((4 * k + 1 - 1) ^ 2 + (4 * k + 1) * (4 * k + 1 - 1) / 2) = 4 * (6 * k * k) + 2 * k := by
    have e1 : 4 * k + 1 - 1 = 4 * k := by omega
    have e2 : (4 * k + 1) * (4 * k) = 2 * ((4 * k + 1) * (2 * k)) := by ring
    rw [e1, e2, Nat.mul_div_cancel_left _ (by norm_num)]
    ring
  rw [hN] at hdet
  rcases mul_eq_zero.mp hq2 with h | h
  · exfalso
    rw [h] at hq
    nlinarith [mul_self_nonneg ((m1 : ℤ) - m3)]
  · rw [h] at hq
    have h' : ((m0 : ℤ) - m2 - 1) * ((m0 : ℤ) - m2 + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact ⟨by linarith, h⟩
    · exfalso
      omega

/-- Helper (arithmetic of the case $p \equiv 3 \pmod 4$): conclude $a = 0$, $b = 1$ from $a^2-b^2=-1$, $ab=0$ and the relations. Arguments as `arith_one`. -/
theorem arith_three (p m0 m1 m2 m3 : ℕ) (hp : p % 4 = 3) (h2 : 2 * (m0 + m2) = p + 1)
    (h3 : 2 * (m1 + m3) + 1 = p) (hdet : (m1 + 2 * m2 + 3 * m3) % 4 = ((p - 1) ^ 2 + p * (p - 1) / 2) % 4)
    (hq : ((m0 : ℤ) - m2) * ((m0 : ℤ) - m2) - ((m1 : ℤ) - m3) * ((m1 : ℤ) - m3) = -1)
    (hq2 : ((m0 : ℤ) - m2) * ((m1 : ℤ) - m3) = 0) : (m0 : ℤ) - m2 = 0 ∧ (m1 : ℤ) - m3 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
  have hN : ((4 * k + 3 - 1) ^ 2 + (4 * k + 3) * (4 * k + 3 - 1) / 2) = 4 * (6 * k * k + 6 * k + 1) + 2 * k + 3 := by
    have e1 : 4 * k + 3 - 1 = 2 * (2 * k + 1) := by omega
    have e2 : (4 * k + 3) * (2 * (2 * k + 1)) = 2 * ((4 * k + 3) * (2 * k + 1)) := by ring
    rw [e1, e2, Nat.mul_div_cancel_left _ (by norm_num)]
    ring
  rw [hN] at hdet
  rcases mul_eq_zero.mp hq2 with h | h
  · rw [h] at hq
    have h' : ((m1 : ℤ) - m3 - 1) * ((m1 : ℤ) - m3 + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact ⟨h, by linarith⟩
    · exfalso
      omega
  · exfalso
    rw [h] at hq
    nlinarith [mul_self_nonneg ((m0 : ℤ) - m2)]

/-- Helper: if $(A + Bi)^2 = \varepsilon$ for integers $A, B, \varepsilon$ then $A^2 - B^2 = \varepsilon$ and $AB = 0$. Arguments: `A`, `B` the integers, `ε` the value, `h` the equation. -/
theorem sq_re_im (A B ε : ℤ) (h : ((A : ℂ) + (B : ℂ) * Complex.I) ^ 2 = (ε : ℂ)) :
    A * A - B * B = ε ∧ A * B = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two] at h1 h2
  constructor
  · exact_mod_cast (by linarith : (A : ℝ) * A - B * B = ε)
  · exact_mod_cast (by linarith : (A : ℝ) * B = 0)

/-- Helper (case $n \equiv 1 \pmod 4$, with $a^2 + b^2 = 1$ instead of the square relation): conclude $a = 1$, $b = 0$. Arguments as `arith_one`. -/
theorem arith_odd_one (p m0 m1 m2 m3 : ℕ) (hp : p % 4 = 1) (h2 : 2 * (m0 + m2) = p + 1)
    (h3 : 2 * (m1 + m3) + 1 = p) (hdet : (m1 + 2 * m2 + 3 * m3) % 4 = ((p - 1) ^ 2 + p * (p - 1) / 2) % 4)
    (hq : ((m0 : ℤ) - m2) * ((m0 : ℤ) - m2) + ((m1 : ℤ) - m3) * ((m1 : ℤ) - m3) = 1) :
    (m0 : ℤ) - m2 = 1 ∧ (m1 : ℤ) - m3 = 0 := by
  have hb : (m1 : ℤ) - m3 = 0 := by
    have hle : ((m1 : ℤ) - m3) * ((m1 : ℤ) - m3) ≤ 1 := by nlinarith [mul_self_nonneg ((m0 : ℤ) - m2)]
    have h1 : (m1 : ℤ) - m3 ≤ 1 := by nlinarith
    have h2' : -1 ≤ (m1 : ℤ) - m3 := by nlinarith
    omega
  rw [hb] at hq
  exact arith_one p m0 m1 m2 m3 hp h2 h3 hdet (by rw [hb]; linarith) (by rw [hb]; ring)

/-- Helper (case $n \equiv 3 \pmod 4$, with $a^2 + b^2 = 1$): conclude $a = 0$, $b = 1$. Arguments as `arith_one`. -/
theorem arith_odd_three (p m0 m1 m2 m3 : ℕ) (hp : p % 4 = 3) (h2 : 2 * (m0 + m2) = p + 1)
    (h3 : 2 * (m1 + m3) + 1 = p) (hdet : (m1 + 2 * m2 + 3 * m3) % 4 = ((p - 1) ^ 2 + p * (p - 1) / 2) % 4)
    (hq : ((m0 : ℤ) - m2) * ((m0 : ℤ) - m2) + ((m1 : ℤ) - m3) * ((m1 : ℤ) - m3) = 1) :
    (m0 : ℤ) - m2 = 0 ∧ (m1 : ℤ) - m3 = 1 := by
  have ha : (m0 : ℤ) - m2 = 0 := by
    have hle : ((m0 : ℤ) - m2) * ((m0 : ℤ) - m2) ≤ 1 := by nlinarith [mul_self_nonneg ((m1 : ℤ) - m3)]
    have h1 : (m0 : ℤ) - m2 ≤ 1 := by nlinarith
    have h2' : -1 ≤ (m0 : ℤ) - m2 := by nlinarith
    omega
  rw [ha] at hq
  exact arith_three p m0 m1 m2 m3 hp h2 h3 hdet (by rw [ha]; linarith) (by rw [ha]; ring)

/-- Helper (case $n \equiv 0 \pmod 4$, $a^2+b^2 = 2$): the multiplicity relations and the determinant relation modulo 4 leave exactly $(a,b) = (1,1)$ or $(-1,-1)$. Arguments: `n` the length, `m0 … m3` the multiplicities, the hypotheses as named. -/
theorem arith_zero (n m0 m1 m2 m3 : ℕ) (hn : n % 4 = 0) (hn0 : 0 < n) (h2 : m0 + m2 = n / 2 + 1)
    (h3 : m1 + m3 + 1 = n / 2)
    (hdet : (m1 + 2 * m2 + 3 * m3) % 4 = ((n - 1) ^ 2 + n * (n - 1) / 2) % 4)
    (hq : ((m0 : ℤ) - m2) * ((m0 : ℤ) - m2) + ((m1 : ℤ) - m3) * ((m1 : ℤ) - m3) = 2) :
    ((m0 : ℤ) - m2 = 1 ∧ (m1 : ℤ) - m3 = 1) ∨ ((m0 : ℤ) - m2 = -1 ∧ (m1 : ℤ) - m3 = -1) := by
  obtain ⟨i, rfl⟩ : ∃ i, n = 4 * i + 4 := ⟨n / 4 - 1, by omega⟩
  have hN : (4 * i + 4 - 1) ^ 2 + (4 * i + 4) * (4 * i + 4 - 1) / 2 = 4 * (6 * i * i + 9 * i + 3) + 2 * i + 3 := by
    have e1 : 4 * i + 4 - 1 = 4 * i + 3 := by omega
    have e2 : (4 * i + 4) * (4 * i + 3) = 2 * ((2 * i + 2) * (4 * i + 3)) := by ring
    rw [e1, e2, Nat.mul_div_cancel_left _ (by norm_num)]
    ring
  rw [hN] at hdet
  have hA : (m0 : ℤ) - m2 ≤ 1 := by nlinarith [mul_self_nonneg ((m1 : ℤ) - m3)]
  have hA' : -1 ≤ (m0 : ℤ) - m2 := by nlinarith [mul_self_nonneg ((m1 : ℤ) - m3)]
  have hB : (m1 : ℤ) - m3 ≤ 1 := by nlinarith [mul_self_nonneg ((m0 : ℤ) - m2)]
  have hB' : -1 ≤ (m1 : ℤ) - m3 := by nlinarith [mul_self_nonneg ((m0 : ℤ) - m2)]
  have hA0 : (m0 : ℤ) - m2 ≠ 0 := by
    intro h; rw [h] at hq
    have : ((m1 : ℤ) - m3) = 1 ∨ ((m1 : ℤ) - m3) = 0 ∨ ((m1 : ℤ) - m3) = -1 := by omega
    rcases this with h | h | h <;> rw [h] at hq <;> norm_num at hq
  have hB0 : (m1 : ℤ) - m3 ≠ 0 := by
    intro h; rw [h] at hq
    have : ((m0 : ℤ) - m2) = 1 ∨ ((m0 : ℤ) - m2) = 0 ∨ ((m0 : ℤ) - m2) = -1 := by omega
    rcases this with h | h | h <;> rw [h] at hq <;> norm_num at hq
  omega

/-- **Cassels, Appendix B, Example 5 (iii)-(v) (p. 390): the sign of the quadratic Gauss sum.** For an odd prime $p$, $\sum_{j \bmod p} e(j^2/p) = \sqrt p$ if $p \equiv 1 \pmod 4$ and $i\sqrt p$ if $p \equiv 3 \pmod 4$. Schur's proof: $\operatorname{tr}F = (m_0-m_2)+i(m_1-m_3)$ has square $\pm1$ (Example 3), $m_0+m_2$ and $m_1+m_3$ are known by (ii), and the determinant (iv) fixes $m_0,\dots,m_3$. Unconditional (no assumed input). Arguments: `p` the prime, `hp2 : p ≠ 2`. *Erratum (iii):* the printed relation reads $(m_1-m_2)^2+(m_3-m_4)^2 = 1$; the indices must be $(m_0-m_2)^2+(m_1-m_3)^2 = 1$ (see `dftMult_sq_sum_prime`). -/
@[kb "cassels1978" "App. B, Ex. 5 (v), p. 390 (the sign of the quadratic Gauss sum)"]
theorem gauss_sum_value (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ x : ZMod p, (ZMod.stdAddChar (x * x) : ℂ) =
      if p % 4 = 1 then ((Real.sqrt p : ℝ) : ℂ) else Complex.I * ((Real.sqrt p : ℝ) : ℂ) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hc : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)
    exact_mod_cast this.ne'
  have hs := dftMult_sum p
  have hT := dftMult_trace p
  have hT2 := trace_sq_prime p hp2
  have hpar := (dftMult_parity p).1 hodd
  have hdet := dftMult_det p
  rw [Fin.sum_univ_four] at hs hdet
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at hdet
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3] at hdet
  set A : ℤ := (dftMult p 0 : ℤ) - dftMult p 2 with hA
  set B : ℤ := (dftMult p 1 : ℤ) - dftMult p 3 with hB
  have hTc : (A : ℂ) + (B : ℂ) * Complex.I = ((Real.sqrt p : ℝ) : ℂ)⁻¹ * ∑ k : ZMod p, (ZMod.stdAddChar (k * k) : ℂ) := by
    rw [← hT, hA, hB]; push_cast; ring
  rw [← hTc] at hT2
  have hmul : ∀ x y : ℂ, ((Real.sqrt p : ℝ) : ℂ)⁻¹ * x = y → x = ((Real.sqrt p : ℝ) : ℂ) * y := by
    intro x y h
    rw [← h]; field_simp
  by_cases h4 : p % 4 = 1
  · simp only [h4, ↓reduceIte] at hT2 ⊢
    have := sq_re_im A B 1 (by simpa using hT2)
    obtain ⟨hAB1, hAB2⟩ := arith_one p _ _ _ _ h4 hpar.1 hpar.2 (by simpa using hdet) this.1 this.2
    rw [hmul _ (A + B * Complex.I) hTc.symm]
    have e1 : (A : ℂ) = 1 := by rw [hA]; exact_mod_cast hAB1
    have e2 : (B : ℂ) = 0 := by rw [hB]; exact_mod_cast hAB2
    rw [e1, e2]; ring
  · simp only [h4, ↓reduceIte] at hT2 ⊢
    have h43 : p % 4 = 3 := by omega
    have := sq_re_im A B (-1) (by simpa using hT2)
    obtain ⟨hAB1, hAB2⟩ := arith_three p _ _ _ _ h43 hpar.1 hpar.2 (by simpa using hdet) this.1 this.2
    rw [hmul _ (A + B * Complex.I) hTc.symm]
    have e1 : (A : ℂ) = 0 := by rw [hA]; exact_mod_cast hAB1
    have e2 : (B : ℂ) = 1 := by rw [hB]; exact_mod_cast hAB2
    rw [e1, e2]; ring

/-- Helper: $\big|\sum_j e(j^2/n)\big|^2 = n\sum_{d:\,2d = 0} e(d^2/n)$ (substitute $j = k + d$ and sum over $k$). Argument: `n` the modulus. -/
theorem gauss_mul_conj (n : ℕ) [NeZero n] :
    (∑ j : ZMod n, (ZMod.stdAddChar (j * j) : ℂ)) * (starRingEnd ℂ) (∑ j : ZMod n, (ZMod.stdAddChar (j * j) : ℂ)) =
      n * ∑ d ∈ Finset.univ.filter (fun d : ZMod n => d + d = 0), (ZMod.stdAddChar (d * d) : ℂ) := by
  classical
  set ψ : AddChar (ZMod n) ℂ := ZMod.stdAddChar with hψ
  have h1 : (starRingEnd ℂ) (∑ j : ZMod n, ψ (j * j)) = ∑ k : ZMod n, ψ (-(k * k)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => (AddChar.map_neg_eq_conj ψ (k * k)).symm
  rw [h1, Finset.sum_mul_sum, Finset.sum_comm]
  have h2 : ∀ k : ZMod n, ∑ j : ZMod n, ψ (j * j) * ψ (-(k * k)) =
      ∑ d : ZMod n, ψ (d * d) * ψ (k * (d + d)) := by
    intro k
    rw [← Equiv.sum_comp (Equiv.addLeft k)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    simp only [Equiv.coe_addLeft]
    congr 1
    ring
  simp_rw [h2]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have h3 : ∀ d : ZMod n, ∑ k : ZMod n, ψ (k * (d + d)) = if d + d = 0 then (n : ℂ) else 0 := by
    intro d
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n), ZMod.card]
    split_ifs <;> simp
  simp_rw [h3]
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp [mul_comm]

/-- Helper: $\big|\sum_{j \bmod n} e(j^2/n)\big|^2 = n$ for odd $n$. Arguments: `n` the modulus, `m` with `hn : n = 2 * m + 1`. -/
theorem gauss_normSq_odd (n m : ℕ) [NeZero n] (hn : n = 2 * m + 1) :
    Complex.normSq (∑ j : ZMod n, (ZMod.stdAddChar (j * j) : ℂ)) = n := by
  classical
  have h := gauss_mul_conj n
  rw [Complex.mul_conj] at h
  have hc := card_self_neg_odd n m hn
  have hf : Finset.univ.filter (fun d : ZMod n => d + d = 0) = {0} := by
    have hc' : (Finset.univ.filter (fun d : ZMod n => d + d = 0)).card = 1 := by
      rw [← hc]
      exact congrArg Finset.card (Finset.filter_congr fun d _ => (neg_eq_iff_add_eq_zero (a := d) (b := d)).symm)
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc'
    have h0 : (0 : ZMod n) ∈ Finset.univ.filter (fun d : ZMod n => d + d = 0) := by simp
    rw [ha] at h0 ⊢
    rw [Finset.mem_singleton.mp h0]
  rw [hf] at h
  simp at h
  exact_mod_cast h

/-- Helper: $\big|\sum_{j \bmod n} e(j^2/n)\big|^2$ is $0$ if $n = 2m$ with $m$ odd and $2n$ if $m$ is even. Arguments: `n` the modulus, `m` with `hn : n = 2 * m`. -/
theorem gauss_normSq_even (n m : ℕ) [NeZero n] (hn : n = 2 * m) :
    Complex.normSq (∑ j : ZMod n, (ZMod.stdAddChar (j * j) : ℂ)) = if m % 2 = 1 then 0 else 2 * n := by
  classical
  have h := gauss_mul_conj n
  rw [Complex.mul_conj] at h
  have hc := card_self_neg_even n m hn
  have hm : 0 < m := by have := NeZero.pos n; omega
  have hm0 : ((m : ℕ) : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd hm hd
    omega
  have hmm : ((m : ℕ) : ZMod n) + (m : ZMod n) = 0 := by
    have : ((2 * m : ℕ) : ZMod n) = 0 := by rw [← hn]; exact ZMod.natCast_self n
    push_cast at this
    linear_combination this
  have hf : Finset.univ.filter (fun d : ZMod n => d + d = 0) = {0, (m : ZMod n)} := by
    have hc' : (Finset.univ.filter (fun d : ZMod n => d + d = 0)).card = 2 := by
      rw [← hc]
      exact congrArg Finset.card (Finset.filter_congr fun d _ => (neg_eq_iff_add_eq_zero (a := d) (b := d)).symm)
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl
      · simp
      · exact hmm
    · rw [hc', Finset.card_pair hm0.symm]
  have hpsi : (ZMod.stdAddChar ((m : ZMod n) * (m : ZMod n)) : ℂ) = (-1) ^ m := by
    have h1 := ZMod.stdAddChar_coe (N := n) (((m * m : ℕ)) : ℤ)
    push_cast at h1
    rw [h1, hn]
    have : (2 * Real.pi * Complex.I * ((m : ℂ) * m) / ((2 * m : ℕ) : ℂ)) = (m : ℂ) * (Real.pi * Complex.I) := by
      have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    rw [this, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  rw [hf, Finset.sum_pair hm0.symm] at h
  simp only [mul_zero, AddChar.map_zero_eq_one, hpsi] at h
  have hmod : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hmod with h0 | h1
  · have : (-1 : ℂ) ^ m = 1 := Even.neg_one_pow (by rw [Nat.even_iff]; exact h0)
    rw [this] at h
    have hh : ¬ (m % 2 = 1) := by omega
    simp only [hh, ↓reduceIte]
    have : ((Complex.normSq (∑ j : ZMod n, (ZMod.stdAddChar (j * j) : ℂ)) : ℝ) : ℂ) = ((2 * n : ℝ) : ℂ) := by
      rw [h]; push_cast; ring
    exact_mod_cast this
  · have : (-1 : ℂ) ^ m = -1 := Odd.neg_one_pow (by rw [Nat.odd_iff]; exact h1)
    rw [this] at h
    simp only [h1, ↓reduceIte]
    have : ((Complex.normSq (∑ j : ZMod n, (ZMod.stdAddChar (j * j) : ℂ)) : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
      rw [h]; push_cast; ring
    exact_mod_cast this

/-- Helper: $\sum_k e(k^2/n) = \sqrt n\,(a + ib)$ with $a = m_0-m_2$, $b = m_1-m_3$, and $(a^2+b^2)\,n = |\sum_k e(k^2/n)|^2$. Argument: `n` the length. -/
theorem trace_data (n : ℕ) [NeZero n] :
    (∑ k : ZMod n, (ZMod.stdAddChar (k * k) : ℂ)) =
      ((Real.sqrt n : ℝ) : ℂ) * (((dftMult n 0 : ℤ) - dftMult n 2 : ℤ) + ((dftMult n 1 : ℤ) - dftMult n 3 : ℤ) * Complex.I) ∧
    ((((dftMult n 0 : ℤ) - dftMult n 2) * ((dftMult n 0 : ℤ) - dftMult n 2) +
        ((dftMult n 1 : ℤ) - dftMult n 3) * ((dftMult n 1 : ℤ) - dftMult n 3)) * n : ℤ) =
      Complex.normSq (∑ k : ZMod n, (ZMod.stdAddChar (k * k) : ℂ)) := by
  have hc : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
    exact_mod_cast this.ne'
  constructor
  · have hT := dftMult_trace n
    push_cast at hT ⊢
    rw [hT]; field_simp
  · have := dftMult_gauss_norm n
    rw [← this]; push_cast; ring

/-- **Cassels, Appendix B, Example 5 (vi), $n$ odd (p. 390; Schur 1921):** $\sum_{j \bmod n} e(j^2/n) = \sqrt n$ for $n \equiv 1 \pmod 4$ and $i\sqrt n$ for $n \equiv 3 \pmod 4$. Arguments: `n` the modulus, `hodd : n % 2 = 1`. -/
@[kb "cassels1978" "App. B, Ex. 5 (vi), p. 390 (Schur: Gauss sum for n odd)"]
theorem schur_gauss_sum_odd (n : ℕ) [NeZero n] (hodd : n % 2 = 1) :
    ∑ k : ZMod n, (ZMod.stdAddChar (k * k) : ℂ) =
      if n % 4 = 1 then ((Real.sqrt n : ℝ) : ℂ) else Complex.I * ((Real.sqrt n : ℝ) : ℂ) := by
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  obtain ⟨h1, h2⟩ := trace_data n
  have hnorm := gauss_normSq_odd n m hm
  rw [hnorm] at h2
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hq : ((dftMult n 0 : ℤ) - dftMult n 2) * ((dftMult n 0 : ℤ) - dftMult n 2) +
      ((dftMult n 1 : ℤ) - dftMult n 3) * ((dftMult n 1 : ℤ) - dftMult n 3) = 1 := by
    have h3 : (((((dftMult n 0 : ℤ) - dftMult n 2) * ((dftMult n 0 : ℤ) - dftMult n 2) +
        ((dftMult n 1 : ℤ) - dftMult n 3) * ((dftMult n 1 : ℤ) - dftMult n 3)) * n : ℤ) : ℝ) = (n : ℝ) * 1 := by
      rw [h2]; ring
    have h4 : ((((dftMult n 0 : ℤ) - dftMult n 2) * ((dftMult n 0 : ℤ) - dftMult n 2) +
        ((dftMult n 1 : ℤ) - dftMult n 3) * ((dftMult n 1 : ℤ) - dftMult n 3) : ℤ) : ℝ) = 1 := by
      push_cast at h3 ⊢
      nlinarith
    exact_mod_cast h4
  have hs := dftMult_sum n
  have hpar := (dftMult_parity n).1 hodd
  have hdet := dftMult_det n
  rw [Fin.sum_univ_four] at hs hdet
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at hdet
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3] at hdet
  rw [h1]
  by_cases h4 : n % 4 = 1
  · obtain ⟨hA, hB⟩ := arith_odd_one n _ _ _ _ h4 hpar.1 hpar.2 (by simpa using hdet) hq
    simp only [h4, ↓reduceIte]
    rw [hA, hB]; simp; try ring
  · have h43 : n % 4 = 3 := by omega
    obtain ⟨hA, hB⟩ := arith_odd_three n _ _ _ _ h43 hpar.1 hpar.2 (by simpa using hdet) hq
    simp only [h4, ↓reduceIte]
    rw [hA, hB]; simp; try ring

/-- **Cassels, Appendix B, Example 5 (vi), $n \equiv 2 \pmod 4$ (p. 390; Schur 1921):** $\sum_{j \bmod n} e(j^2/n) = 0$. Arguments: `n` the modulus, `hn : n % 4 = 2`. -/
@[kb "cassels1978" "App. B, Ex. 5 (vi), p. 390 (Schur: Gauss sum for n ≡ 2 mod 4)"]
theorem schur_gauss_sum_two (n : ℕ) [NeZero n] (hn : n % 4 = 2) :
    ∑ k : ZMod n, (ZMod.stdAddChar (k * k) : ℂ) = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have := gauss_normSq_even n m hm
  simp only [show m % 2 = 1 by omega, ↓reduceIte] at this
  exact Complex.normSq_eq_zero.mp (by simpa using this)

/-- **Cassels, Appendix B, Example 5 (vi), $n \equiv 0 \pmod 4$ (p. 390; Schur 1921), up to a sign:** $\sum_{j \bmod n} e(j^2/n) = \pm(1+i)\sqrt n$. The printed value is $(1+i)\sqrt n$ (the plus sign). The method of this file (eigenvalue multiplicities from the absolute value of the trace, (ii) and the determinant (iv)) leaves exactly the two possibilities $(m_0-m_2,\,m_1-m_3) = (1,1)$ and $(-1,-1)$ in this case, which have the same determinant and the same trace squared; the remaining sign needs one more input (not formalized). Arguments: `n` the modulus, `hn : n % 4 = 0`. -/
@[kb "cassels1978" "App. B, Ex. 5 (vi), p. 390 (Schur: Gauss sum for n ≡ 0 mod 4, up to sign)"]
theorem schur_gauss_sum_zero (n : ℕ) [NeZero n] (hn : n % 4 = 0) :
    ∑ k : ZMod n, (ZMod.stdAddChar (k * k) : ℂ) = (1 + Complex.I) * ((Real.sqrt n : ℝ) : ℂ) ∨
    ∑ k : ZMod n, (ZMod.stdAddChar (k * k) : ℂ) = -((1 + Complex.I) * ((Real.sqrt n : ℝ) : ℂ)) := by
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  obtain ⟨h1, h2⟩ := trace_data n
  have hnorm := gauss_normSq_even n m hm
  simp only [show ¬ (m % 2 = 1) by omega, ↓reduceIte] at hnorm
  rw [hnorm] at h2
  have hq : ((dftMult n 0 : ℤ) - dftMult n 2) * ((dftMult n 0 : ℤ) - dftMult n 2) +
      ((dftMult n 1 : ℤ) - dftMult n 3) * ((dftMult n 1 : ℤ) - dftMult n 3) = 2 := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    have h3 : (((((dftMult n 0 : ℤ) - dftMult n 2) * ((dftMult n 0 : ℤ) - dftMult n 2) +
        ((dftMult n 1 : ℤ) - dftMult n 3) * ((dftMult n 1 : ℤ) - dftMult n 3)) * n : ℤ) : ℝ) = (n : ℝ) * 2 := by
      rw [h2]; push_cast; ring
    have h4 : ((((dftMult n 0 : ℤ) - dftMult n 2) * ((dftMult n 0 : ℤ) - dftMult n 2) +
        ((dftMult n 1 : ℤ) - dftMult n 3) * ((dftMult n 1 : ℤ) - dftMult n 3) : ℤ) : ℝ) = 2 := by
      push_cast at h3 ⊢
      nlinarith
    exact_mod_cast h4
  have hs := dftMult_sum n
  have hpar := (dftMult_parity n).2 (by omega)
  have hdet := dftMult_det n
  rw [Fin.sum_univ_four] at hs hdet
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at hdet
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3] at hdet
  rw [h1]
  rcases arith_zero n _ _ _ _ hn (NeZero.pos n) hpar.1 hpar.2 (by simpa using hdet) hq with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · left; rw [hA, hB]; simp; ring
  · right; rw [hA, hB]; simp; ring

/-- **Cassels, Appendix B, Example 5 (iv), p. 390:** $\det F = i^{(n-1)^2 + n(n-1)/2}$ (the exact value; a fourth root of unity). Argument: `n` the length. -/
@[kb "cassels1978" "App. B, Ex. 5 (iv), p. 390 (det F = i^((n-1)^2 + n(n-1)/2))"]
theorem dftLin_det (n : ℕ) [NeZero n] :
    LinearMap.det (dftLin n) = Complex.I ^ ((n - 1) ^ 2 + n * (n - 1) / 2) := by
  have h1 := det_eq_eigMult _ (dftLin_pow_four n)
  have h2 : ∏ u : Fin 4, (Complex.I ^ (u : ℕ)) ^ eigMult (dftLin n) u =
      Complex.I ^ (∑ u : Fin 4, (u : ℕ) * dftMult n u) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl (fun u _ => ?_)
    rw [← pow_mul]; rfl
  rw [h1, h2, Complex.I_pow_eq_pow_mod, dftMult_det n, ← Complex.I_pow_eq_pow_mod]

/-- **Cassels, Appendix B, Example 5 (iii), second part (p. 390):** for an odd prime $p$, $(m_0-m_2)^2 + (m_1-m_3)^2 = 1$. *Erratum:* the printed relation $(m_1-m_2)^2 + (m_3-m_4)^2 = 1$ must read $(m_0-m_2)^2 + (m_1-m_3)^2 = 1$, because the trace is $(m_0 - m_2) + i(m_1-m_3)$ and there are only the four multiplicities $m_0,\dots,m_3$; confirmed by the Lean statement (proved from $|\tau(\chi,p)|^2 = p$). Arguments: `p` the prime, `hp2 : p ≠ 2`. -/
@[kb "cassels1978" "App. B, Ex. 5 (iii), p. 390 ((m_0-m_2)^2 + (m_1-m_3)^2 = 1; index erratum)"]
theorem dftMult_sq_sum_prime (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ((dftMult p 0 : ℤ) - dftMult p 2) ^ 2 + ((dftMult p 1 : ℤ) - dftMult p 3) ^ 2 = 1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have h := dftMult_gauss_norm p
  rw [gauss_normSq_odd p (p / 2) (by omega)] at h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have h' : ((((dftMult p 0 : ℤ) - dftMult p 2) ^ 2 + ((dftMult p 1 : ℤ) - dftMult p 3) ^ 2 : ℤ) : ℝ) = 1 := by
    have : ((((dftMult p 0 : ℤ) - dftMult p 2) ^ 2 + ((dftMult p 1 : ℤ) - dftMult p 3) ^ 2 : ℤ) : ℝ) * p = 1 * p := by
      rw [one_mul]; exact_mod_cast h
    exact mul_right_cancel₀ hp0.ne' this
  exact_mod_cast h'

/-- **Cassels, Appendix B, Example 5 (iii), first part (p. 390):** for an odd prime $p$, $\operatorname{tr}F = (\sqrt p)^{-1}\tau(\chi,p)$ with $\chi$ the quadratic character (`quadDir p`) and $\tau(\chi,p)=\sum_r\chi(r)e(r/p)$. Arguments: `p` the prime, `hp2 : p ≠ 2`. -/
@[kb "cassels1978" "App. B, Ex. 5 (iii), p. 390 (tr F = τ(χ,p)/√p)"]
theorem trace_dftLin_prime (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    LinearMap.trace ℂ _ (dftLin p) =
      ((Real.sqrt p : ℝ) : ℂ)⁻¹ * ∑ r : ZMod p, quadDir p r * ZMod.stdAddChar r := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [trace_dftLin, sum_sq_eq_gauss p hp2]

/-- **Cassels, Appendix B, Example 5 (v), p. 390:** $\tau(\chi,p) = \sqrt p$ for $p \equiv 1 \pmod 4$ and $i\sqrt p$ for $p \equiv 3 \pmod 4$, for $\chi$ the quadratic character (`quadDir p`). Arguments: `p` the prime, `hp2 : p ≠ 2`. -/
@[kb "cassels1978" "App. B, Ex. 5 (v), p. 390 (τ(χ,p) = √p or i√p)"]
theorem gauss_sum_tau (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ r : ZMod p, quadDir p r * ZMod.stdAddChar r =
      if p % 4 = 1 then ((Real.sqrt p : ℝ) : ℂ) else Complex.I * ((Real.sqrt p : ℝ) : ℂ) := by
  rw [← sum_sq_eq_gauss p hp2]
  exact gauss_sum_value p hp2

end QuadFormsKB.Cassels
