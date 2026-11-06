/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ for binary lattices

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 and the remark after it: *the integral automorphisms of a lattice are usually, but
not always, products of integral reflections.* This file shows that they always are in dimension $n = 2$, at every
finite prime of every number field (including the primes over $2$), and so removes the binary lattices from the
residual statement of the "only if" direction of Theorem 18 at $p = 2$.

**Layer.** As in `Section9Theorem18Generated.lean`: a finite prime $\mathfrak p$ of a number field $F$, a
nondegenerate form $Q$ on $F_\mathfrak p^n$ with bilinear form $B(x, y) = Q(x + y) - Q(x) - Q(y)$ (`qbil`), a lattice
$L$ with localization $L_\mathfrak p$ (`loc v L.1`), a basis $b_k = \gamma e_k$ of $L_\mathfrak p$ with Gram matrix
$G = \gamma^{\mathsf T}H\gamma$ (`locGram`, $G_{kk} = 2Q(b_k)$), the reflections $\tau_x$ (`symm`), the integral
automorphisms $O(L_\mathfrak p)$ (`locStabV`) and the $p$-adic root vectors (`IsRootVector`: $Q(x) \ne 0$ and
$\tau_x \in O(L_\mathfrak p)$).

**Defines**
* `Theorem18DyadicCovered3 Q L v` (the **shape predicate**, third version): the shapes of `Theorem18DyadicCovered2`
  or $n = 2$;
* `Theorem18DyadicResidual3` (a **named statement**, smaller than `Theorem18DyadicResidual2`): the "only if"
  direction at the prime over $2$ for every lattice **not** covered by `Theorem18DyadicCovered3`.

**Proves**
* `exists_rootVector_of_max` (**a root vector of maximal norm**): for $n \ge 1$ and nondegenerate $Q$, every lattice
  $L$ has a $p$-adic root vector, namely a vector $x \in L_\mathfrak p$ at which $\lvert Q \rvert$ attains its maximum
  over $L_\mathfrak p$ (the maximum exists because $\lvert Q \rvert$ is bounded on $L_\mathfrak p$ and takes values in
  the discrete value group); then $\lvert B(x, y)\rvert \le \lvert Q(x)\rvert$ for $y \in L_\mathfrak p$, so
  $\tau_x(L_\mathfrak p) = L_\mathfrak p$;
* `binary_improper_mul_self` and `binary_improper_eq_symm` (**an improper isometry of a nondegenerate binary space is
  a reflection**): for $n = 2$, $\rho \in O(V)$ with $\det\rho = -1$ has trace $0$ (compare $\operatorname{tr}\rho^{-1}$
  computed from the adjugate and from $\rho^{-1} = H^{-1}\rho^{\mathsf T}H$), hence $\rho^2 = 1$ by Cayley–Hamilton,
  hence $\rho$ has an eigenvector $w$ with eigenvalue $-1$ and an eigenvector $u$ with eigenvalue $+1$, which are
  orthogonal, linearly independent, and $w$ is anisotropic because $V$ is nondegenerate; so $\rho = \tau_w$;
* `generatedByRootReflections_of_binary` (**binary lattices**): for $n = 2$, every $\sigma \in O(L_\mathfrak p)$ is a
  product of at most two reflections in $p$-adic root vectors (Conway–Sloane's remark, p. 391);
* `theorem18OnlyIf_of_binary`, `theorem18OnlyIf_of_covered3`, `theorem18DyadicResidual2_of_residual3`,
  `theorem18Dyadic_of_residual3`, `theorem18Statement_of_residual3`: the consequences for Theorem 18 at $p = 2$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicGlue2
import QuadFormsKB.Literature.ConwaySloane.Section3BinarySpinorNorm
import QuadFormsKB.Literature.Cassels.Ch11Sec4Thm

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices EstesPall

/-! ### Improper isometries of a binary space -/

section BinaryImproper

variable {F : Type*} [Field F] [NumberField F] (Q : QuadForm F 2) (K : Type*) [Field K] [Algebra F K]
  [CharZero K]

/-- Two vectors $w, u \in K^2$ with $\det[w \mid u] = 0$ and $w \ne 0$ are proportional. -/
theorem exists_smul_of_det_eq_zero {w u : Fin 2 → K} (hw : w ≠ 0) (hd : w 0 * u 1 - u 0 * w 1 = 0) :
    ∃ c : K, u = c • w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨u 1 / w 1, ?_⟩
    have hu0 : u 0 * w 1 = 0 := by linear_combination -hd + u 1 * h0
    have hu0' : u 0 = 0 := (mul_eq_zero.mp hu0).resolve_right h1
    funext i
    fin_cases i
    · simp [h0, hu0']
    · simp; field_simp
  · refine ⟨u 0 / w 0, ?_⟩
    funext i
    fin_cases i
    · simp; field_simp
    · simp; field_simp; linear_combination hd

/-- A vector $h \in K^2$ orthogonal (for the standard dot product) to two vectors $w, u$ with
$\det[w \mid u] \ne 0$ is zero. -/
theorem eq_zero_of_dot_dot {w u h : Fin 2 → K} (hd : w 0 * u 1 - u 0 * w 1 ≠ 0)
    (h1 : w 0 * h 0 + w 1 * h 1 = 0) (h2 : u 0 * h 0 + u 1 * h 1 = 0) : h = 0 := by
  have e0 : h 0 * (w 0 * u 1 - u 0 * w 1) = 0 := by linear_combination u 1 * h1 - w 1 * h2
  have e1 : h 1 * (w 0 * u 1 - u 0 * w 1) = 0 := by linear_combination w 0 * h2 - u 0 * h1
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp e0).resolve_right hd
  · exact (mul_eq_zero.mp e1).resolve_right hd

/-- **An improper isometry of a nondegenerate binary space is an involution**: if $\rho \in O(V)$ with
$\det\rho = -1$ and $n = 2$, then $\rho^2 = 1$. (Its trace is $0$: $\operatorname{tr}\rho^{-1} = \operatorname{tr}\rho$
since $\rho^{-1} = H^{-1}\rho^{\mathsf T}H$, while $\rho^{-1} = -\operatorname{adj}\rho$ has trace
$-\operatorname{tr}\rho$ for $\det\rho = -1$; then use Cayley–Hamilton.) -/
theorem binary_improper_mul_self (hQ : Q.Nondegenerate) (ρ : orthGroup Q K)
    (hdet : (ρ : GL (Fin 2) K).val.det = -1) :
    (ρ : GL (Fin 2) K).val * (ρ : GL (Fin 2) K).val = 1 := by
  set M := (ρ : GL (Fin 2) K).val with hM
  set H := Q.hessian.map (algebraMap F K) with hH
  have horth : Mᵀ * H * M = H := (mem_orthGroup Q).mp ρ.2
  have hHdet : H.det ≠ 0 := by
    rw [hH, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).mpr hQ
  have hHu : IsUnit H.det := isUnit_iff_ne_zero.mpr hHdet
  have h1 : M * M.adjugate = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.mul_adjugate, hdet]
  have hA : H * M.adjugate = -(Mᵀ * H) := by
    calc H * M.adjugate = (Mᵀ * H * M) * M.adjugate := by rw [horth]
      _ = Mᵀ * H * (M * M.adjugate) := by rw [Matrix.mul_assoc]
      _ = -(Mᵀ * H) := by rw [h1]; simp
  have hadj : M.adjugate = -(H⁻¹ * (Mᵀ * H)) := by
    calc M.adjugate = H⁻¹ * (H * M.adjugate) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHu, Matrix.one_mul]
      _ = _ := by rw [hA, Matrix.mul_neg]
  have htr1 : M.adjugate.trace = M.trace := by
    rw [Matrix.adjugate_fin_two]; simp [Matrix.trace_fin_two]; ring
  have htr2 : M.adjugate.trace = -M.trace := by
    rw [hadj, Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hHu,
      Matrix.mul_one, Matrix.trace_transpose]
  have h2 : (2 : K) * M.trace = 0 := by linear_combination htr2 - htr1
  have htr0 : M.trace = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hd2 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = -1 := by
    rw [← hdet, Matrix.det_fin_two]
  have ht : M 0 0 + M 1 1 = 0 := by rwa [Matrix.trace_fin_two] at htr0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination M 0 0 * ht - hd2
  · linear_combination M 0 1 * ht
  · linear_combination M 1 0 * ht
  · linear_combination M 1 1 * ht - hd2

/-- **An improper isometry of a nondegenerate binary space is a reflection** (O'Meara 1963, 43:3 for $n = 2$): if
$n = 2$, $Q$ is nondegenerate and $\rho \in O(V)$ has $\det\rho = -1$, then $\rho = \tau_w$ for an anisotropic
vector $w$. -/
@[kb "omeara1963" "§43B, 43:3, p. 102 (n = 2: an improper isometry of a binary space is a symmetry)"]
theorem binary_improper_eq_symm (hQ : Q.Nondegenerate) (ρ : orthGroup Q K)
    (hdet : (ρ : GL (Fin 2) K).val.det = -1) :
    ∃ w : Fin 2 → K, Q.evalIn K w ≠ 0 ∧ ρ = symm Q K w := by
  have hMM := binary_improper_mul_self Q K hQ ρ hdet
  set M := (ρ : GL (Fin 2) K).val with hM
  have hH : (Q.hessian.map (algebraMap F K)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).mpr hQ
  -- an eigenvector for `-1` and one for `+1`
  obtain ⟨v₁, hv₁⟩ : ∃ v : Fin 2 → K, M *ᵥ v - v ≠ 0 := by
    by_contra h
    push Not at h
    have h1 : M = 1 := eq_one_of_fix_basis K (Pi.basisFun K (Fin 2)) fun i => sub_eq_zero.mp (h _)
    rw [h1, Matrix.det_one] at hdet
    norm_num at hdet
  obtain ⟨v₂, hv₂⟩ : ∃ v : Fin 2 → K, M *ᵥ v + v ≠ 0 := by
    by_contra h
    push Not at h
    have h1 : -M = 1 := eq_one_of_fix_basis K (Pi.basisFun K (Fin 2)) fun i => by
      rw [Matrix.neg_mulVec]; exact neg_eq_iff_eq_neg.mpr (eq_neg_of_add_eq_zero_left (h _))
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_neg, hdet, Matrix.det_one] at h2
    norm_num at h2
  set w := M *ᵥ v₁ - v₁ with hw
  set u := M *ᵥ v₂ + v₂ with hu
  have hMw : M *ᵥ w = -w := by
    rw [hw, mulVec_sub, mulVec_mulVec, hMM, Matrix.one_mulVec]; abel
  have hMu : M *ᵥ u = u := by
    rw [hu, mulVec_add, mulVec_mulVec, hMM, Matrix.one_mulVec, add_comm]
  -- orthogonality
  have hwu : qbil Q K w u = 0 := by
    have h := qbil_orth Q K ρ w u
    change qbil Q K (M *ᵥ w) (M *ᵥ u) = _ at h
    rw [hMw, hMu, qbil_neg_left] at h
    have h2 : (2 : K) * qbil Q K w u = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  -- independence
  have hdetwu : w 0 * u 1 - u 0 * w 1 ≠ 0 := by
    intro hd
    obtain ⟨c, hc⟩ := exists_smul_of_det_eq_zero K hv₁ hd
    apply hv₂
    have h1 : M *ᵥ u = -u := by rw [hc, mulVec_smul, hMw, smul_neg]
    have h2 : u = 0 := by
      have : (2 : K) • u = 0 := by rw [two_smul]; nth_rewrite 1 [← hMu]; rw [h1]; simp
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero
    exact h2
  -- `w` is anisotropic
  have hQw : Q.evalIn K w ≠ 0 := by
    intro h0
    have hww : w ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ w) = 0 := by
      rw [← two_mul_evalIn Q, h0, mul_zero]
    have huw : u ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ w) = 0 := by
      have : qbil Q K u w = 0 := by rw [qbil_comm]; exact hwu
      exact this
    have hz := eq_zero_of_dot_dot K (h := Q.hessian.map (algebraMap F K) *ᵥ w) hdetwu
      (by simpa [dotProduct, Fin.sum_univ_two] using hww) (by simpa [dotProduct, Fin.sum_univ_two] using huw)
    exact hv₁ (Matrix.eq_zero_of_mulVec_eq_zero hH hz)
  refine ⟨w, hQw, ?_⟩
  have hd' : (colMat K w u).det ≠ 0 := by rw [det_colMat]; exact hdetwu
  refine Subtype.ext (Units.ext (eq_of_colMat K hd' ?_ ?_))
  · show M *ᵥ w = ((symm Q K w : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w
    rw [hMw, symm_mulVec_bil Q K hQw, qbil_self, mul_div_cancel_right₀ _ hQw, two_smul]
    abel
  · show M *ᵥ u = ((symm Q K w : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u
    rw [hMu, symm_fix Q K hwu]

end BinaryImproper

/-! ### A root vector of maximal norm -/

section MaxNorm

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) (L : Lat F n)
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **A $p$-adic root vector of maximal norm** (Conway–Sloane §9.5, p. 391, the remark on binary lattices): for
$n \ge 1$ and nondegenerate $Q$, every lattice $L$ has a $p$-adic root vector. Indeed $\lvert Q\rvert$ is bounded on
$L_\mathfrak p$ (in a basis $b = \gamma e$ with Gram matrix $G$, $2Q(\gamma c) = c^{\mathsf T}Gc$), takes values in the
discrete group $e^{\mathbb Z}$, and is not identically $0$ (else $G = 0$); so it attains a maximum $\lvert Q(x)\rvert
\ne 0$ on $L_\mathfrak p$, and then $\lvert B(x, y)\rvert \le \max(\lvert Q(x+y)\rvert, \lvert Q(x)\rvert,
\lvert Q(y)\rvert) \le \lvert Q(x)\rvert$ for $y \in L_\mathfrak p$, whence $\tau_x(L_\mathfrak p) = L_\mathfrak p$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (every lattice has a p-adic root vector: a vector of maximal norm)"]
theorem exists_rootVector_of_max (hQ : Q.Nondegenerate) (hn : 0 < n) : ∃ x, IsRootVector Q L v x := by
  classical
  obtain ⟨γ, hγ⟩ := exists_locAct_std_model v L
  have hmem : ∀ c ∈ std v, γ.val *ᵥ c ∈ (loc v L.1) := fun c hc => by rw [hγ]; exact ⟨c, hc, rfl⟩
  have hbasis : ∀ i : Fin n, γ.val *ᵥ Pi.single i 1 ∈ (loc v L.1) := fun i =>
    hmem _ (single_mem_std i (by simp))
  -- boundedness
  have hbound : ∃ B : ℤ, ∀ y ∈ (loc v L.1), Valued.v (Q.evalIn Fv y) ≤ exp B := by
    choose k hk using fun i j => exists_valued_le v (locGram Q v γ i j)
    set N : ℕ := Finset.univ.sup (fun p : Fin n × Fin n => k p.1 p.2) with hN
    obtain ⟨k2, hk2⟩ := exists_valued_le v (2⁻¹ : Fv)
    refine ⟨(k2 : ℤ) + N, fun y hy => ?_⟩
    rw [hγ, mem_locAct] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have hc' := mem_std_iff.mp hc
    have hG : ∀ i j, Valued.v (locGram Q v γ i j) ≤ exp (N : ℤ) := fun i j =>
      (hk i j).trans (exp_le_exp.mpr (by
        exact_mod_cast Finset.le_sup (f := fun p : Fin n × Fin n => k p.1 p.2) (Finset.mem_univ (i, j))))
    have hdot : Valued.v (c ⬝ᵥ (locGram Q v γ *ᵥ c)) ≤ exp (N : ℤ) := by
      unfold dotProduct
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul]
      have hin : Valued.v ((locGram Q v γ *ᵥ c) i) ≤ exp (N : ℤ) := by
        unfold mulVec dotProduct
        refine Valuation.map_sum_le _ fun j _ => ?_
        rw [map_mul]
        calc _ ≤ exp (N : ℤ) * 1 := mul_le_mul' (hG i j) (hc' j)
          _ = _ := mul_one _
      calc _ ≤ 1 * exp (N : ℤ) := mul_le_mul' (hc' i) hin
        _ = _ := one_mul _
    have hQy : Q.evalIn Fv (γ.val *ᵥ c) = 2⁻¹ * (c ⬝ᵥ (locGram Q v γ *ᵥ c)) := by
      rw [← two_mul_evalIn_locGram]; field_simp
    rw [hQy, map_mul]
    calc Valued.v (2⁻¹ : Fv) * Valued.v (c ⬝ᵥ (locGram Q v γ *ᵥ c))
        ≤ exp (k2 : ℤ) * exp (N : ℤ) := mul_le_mul' hk2 hdot
      _ = _ := (exp_add _ _).symm
  -- not identically zero
  have hnz : ∃ y ∈ (loc v L.1), Q.evalIn Fv y ≠ 0 := by
    by_contra hall
    push Not at hall
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hG0 : locGram Q v γ = 0 := by
      ext i j
      rw [← locGram_apply_eq, qbil_eq_polar, hall _ ((loc v L.1).add_mem (hbasis i) (hbasis j)), hall _ (hbasis i),
        hall _ (hbasis j)]
      simp
    exact locGram_det_ne_zero hQ γ (by rw [hG0]; exact Matrix.det_zero)
  obtain ⟨B, hB⟩ := hbound
  obtain ⟨y0, hy0M, hy00⟩ := hnz
  obtain ⟨k1, hk1⟩ := exists_valued_eq_exp v hy00
  obtain ⟨k0, ⟨x, hxM, hx0, hxk⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun k : ℤ => ∃ y ∈ (loc v L.1), Q.evalIn Fv y ≠ 0 ∧ Valued.v (Q.evalIn Fv y) = exp k)
    ⟨B, fun k ⟨y, hyM, _, hyk⟩ => by
      have := hB y hyM
      rw [hyk, exp_le_exp] at this
      exact this⟩
    ⟨k1, y0, hy0M, hy00, hk1⟩
  have hle : ∀ z ∈ (loc v L.1), Valued.v (Q.evalIn Fv z) ≤ exp k0 := by
    intro z hz
    by_cases hz0 : Q.evalIn Fv z = 0
    · rw [hz0, map_zero]; exact zero_le
    · obtain ⟨k', hk'⟩ := exists_valued_eq_exp v hz0
      rw [hk', exp_le_exp]
      exact hmax k' ⟨z, hz, hz0, hk'⟩
  refine ⟨x, hx0, ?_⟩
  show locAct v (symm Q Fv x : GL (Fin n) Fv) (loc v L.1) = loc v L.1
  refine locAct_symm_eq hxM hx0 fun y hy => ?_
  rw [qbil_eq_polar, hxk]
  refine Valuation.map_sub_le _ (Valuation.map_sub_le _ (hle _ ((loc v L.1).add_mem hxM hy)) (hxk.le)) (hle _ hy)

end MaxNorm

/-! ### Binary lattices -/

section Binary

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F

/-- **The integral automorphisms of a binary lattice are products of integral reflections** (Conway–Sloane §9.5,
p. 391, the remark after Theorem 18, in dimension $n = 2$; true at every finite prime of every number field,
including the primes over $2$): for $n = 2$ and nondegenerate $Q$, every $\sigma \in O(L_\mathfrak p)$ is
$\tau_w$ or $\tau_w\tau_r$ for $p$-adic root vectors $w, r$. If $\det\sigma = -1$ then $\sigma = \tau_w$
(`binary_improper_eq_symm`) and $w$ is a root vector because $\tau_w = \sigma \in O(L_\mathfrak p)$. If
$\det\sigma = 1$, take a root vector $r$ of maximal norm (`exists_rootVector_of_max`); then $\sigma\tau_r \in
O(L_\mathfrak p)$ is improper, $= \tau_w$, and $\sigma = \tau_w\tau_r$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (remark after Thm. 18: binary lattices, integral automorphisms are products of integral reflections)"]
theorem generatedByRootReflections_of_binary (hQ : Q.Nondegenerate) (hn : n = 2) (L : Lat F n) :
    GeneratedByRootReflections Q v L := by
  subst hn
  intro σ hσ
  have key : ∀ τ : orthGroup Q Fv, τ ∈ locStabV Q v L → (τ : GL (Fin 2) Fv).val.det = -1 →
      ∃ w, IsRootVector Q L v w ∧ τ = symm Q Fv w := by
    intro τ hτ hdet
    obtain ⟨w, hw, hτw⟩ := binary_improper_eq_symm Q Fv hQ τ hdet
    exact ⟨w, ⟨hw, hτw ▸ hτ⟩, hτw⟩
  rcases Tamagawa.det_eq_one_or_neg_one Q hQ σ with h | h
  · obtain ⟨r, hr⟩ := exists_rootVector_of_max Q L v hQ (by norm_num)
    have hdet : ((σ * symm Q Fv r : orthGroup Q Fv) : GL (Fin 2) Fv).val.det = -1 := by
      change ((σ : GL (Fin 2) Fv).val * (symm Q Fv r : GL (Fin 2) Fv).val).det = -1
      rw [det_mul, h, symm_det Q Fv hr.1, one_mul]
    obtain ⟨w, hw, hσw⟩ := key _ (mul_mem hσ hr.2) hdet
    refine ⟨[w, r], ?_, ?_⟩
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      exacts [hw, hr]
    · have : σ = (σ * symm Q Fv r) * symm Q Fv r := by rw [mul_assoc, symm_mul_self, mul_one]
      rw [this, hσw]
      simp [symmProd]
  · obtain ⟨w, hw, hσw⟩ := key σ hσ h
    exact ⟨[w], by simpa using hw, by simp [symmProd, hσw]⟩

variable {Q} {L : Lat F n}

/-- **Theorem 18, "only if", for binary lattices** (every finite prime of every number field; Conway–Sloane §9.5,
p. 391): for $n = 2$ the condition holds for every lattice. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 ('only if', binary lattices)"]
theorem theorem18OnlyIf_of_binary (hQ : Q.Nondegenerate) (hn : n = 2) :
    Theorem18OnlyIf Q L v hQ :=
  theorem18OnlyIf_of_generated hQ (generatedByRootReflections_of_binary Q hQ hn L)

end Binary

/-! ### The enlarged shape predicate and the smaller residual statement -/

section Shape

variable {n : ℕ}

/-- **The $2$-adic shapes for which Theorem 18 ("only if") is proved, third version**: the shapes of
`Theorem18DyadicCovered2` (those of `Theorem18DyadicCovered`, or $L_2 = 2^k(E \perp \langle 2u\rangle)$ with $E$ even
unimodular), or $n = 2$ (binary lattices, `generatedByRootReflections_of_binary`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the 2-adic shapes proved in the library, third version)"]
def Theorem18DyadicCovered3 (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  Theorem18DyadicCovered2 Q L v ∨ n = 2

/-- **Theorem 18, "only if", at $p = 2$ on the covered shapes, third version** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the covered 2-adic shapes, third version)"]
theorem theorem18OnlyIf_of_covered3 {Q : QuadForm ℚ n} (hQ : Q.Nondegenerate) {L : Lat ℚ n}
    {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (hc : Theorem18DyadicCovered3 Q L v) :
    Theorem18OnlyIf Q L v hQ := by
  rcases hc with hc | hn
  · exact theorem18OnlyIf_of_covered2 hQ h2 hc
  · exact theorem18OnlyIf_of_binary hQ hn

end Shape

/-- **Theorem 18 at $p = 2$, "only if", for the residual lattices, third version** (Conway–Sloane §9.5, p. 391,
"based on Theorem 81 of [Wat3]", G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every
regular form $Q$ over $\mathbb Q$, lattice $L$ and the prime $v$ over $2$ such that $L_2$ is **not** of a shape
covered by `Theorem18DyadicCovered3`, every $2$-adically automorphous number $A \in \theta(O^+(L_2))$ is, up to
squares, the product of the norms of an even number of $2$-adic root vectors (`Theorem18OnlyIf`).

It implies `Theorem18DyadicResidual2` (`theorem18DyadicResidual2_of_residual3`), hence `Theorem18Dyadic`. The
remaining lattices are those with $n \ne 2$ outside the earlier shapes. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', lattices outside the proved 2-adic shapes, third version; stated; Watson 1960, Thm. 81)"]
structure Theorem18DyadicResidual3 : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ¬ Theorem18DyadicCovered3 Q L v →
      Theorem18OnlyIf Q L v hQ

/-- **The second residual statement from the third**: binary lattices are proved
(`theorem18OnlyIf_of_binary`), elsewhere it is `Theorem18DyadicResidual3`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': residual shapes from the third residual statement)"]
theorem theorem18DyadicResidual2_of_residual3 (h : Theorem18DyadicResidual3) : Theorem18DyadicResidual2 where
  exists_rootVectors n Q hQ L v h2 hnc := by
    by_cases hn : n = 2
    · exact theorem18OnlyIf_of_binary hQ hn
    · exact h.exists_rootVectors n Q hQ L v h2 (fun hc => hc.elim hnc hn)

/-- **`Theorem18Dyadic` from the third residual statement.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', conditional on the residual shapes, third version)"]
theorem theorem18Dyadic_of_residual3 (h : Theorem18DyadicResidual3) : Theorem18Dyadic :=
  theorem18Dyadic_of_residual2 (theorem18DyadicResidual2_of_residual3 h)

/-- **Conway–Sloane's Theorem 18 from the third residual statement**: the full Theorem 18 (`Theorem18Statement`,
every prime, both directions) follows from `Theorem18DyadicResidual3`; everything else is proved. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the residual 2-adic shapes, third version)"]
theorem theorem18Statement_of_residual3 (h : Theorem18DyadicResidual3) : Theorem18Statement :=
  theorem18Statement_of_residual2 (theorem18DyadicResidual2_of_residual3 h)

end QuadFormsKB.ConwaySloane
