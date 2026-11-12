import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Theorem751
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Theorem751Trace

/-!
# Kitaoka 1993, Theorem 7.5.1: the induction on the rank

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.5, Theorem 7.5.1, p. 242 (printed page).

Let $K$ be totally real, $L = (\mathbb Z^n, A)$, $M = (\mathbb Z^n, B)$ positive lattices and
$\sigma : R_K L \cong R_K M$ an isometry, a matrix $P$ over $R_K$ with $\det P \in R_K^\times$ and
$P^{\mathsf T} B P = A$ over $K$ (`IsScalarExtensionIsometry`). This file proves $P \in M_n(\mathbb Z)$
(i.e. $\sigma(L) = M$) under the hypothesis that minimal tensors of $L' \otimes (R_K, B_K)$ split for every positive
lattice $L'$ of rank at most $n$ (`SplitOK`): `integral_of_splitOK`.

**Proof** (Kitaoka's, in matrix form). Induction on $n$. Let $x$ be a minimal vector of $L$; by Lemma 7.5.5
(`first_col`) $y = Px$ is a minimal vector of $M$. Both are primitive, so they are first columns of unimodular
matrices $U$, $V$ (`exists_unimodular`). In the new bases $U^{\mathsf T} A U$, $V^{\mathsf T} B V$ the isometry
$P' = V^{-1} P U$ has first column $e_0$. Its lower right block $P''$ is an isometry between the Schur complements
(the projections of $L$, $M$ to the orthogonal complements of $x$, $y$; `schur_rel`, `schur_pos`), hence integral by
induction; the first row of $P'$ is then rational, and in $R_K$, hence integral (`int_of_rat`).
-/

open Matrix NumberField

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

/-- **Unimodular congruence preserves positivity**: if $U$ is an integer matrix with integer inverse $U^{-1}$ and $A$
is a positive Gram matrix then so is $U^{\mathsf T} A U$ (from `isPosGram_conj`). -/
theorem isPosGram_conj_unimod {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} (hA : IsPosGram A)
    {U Ui : Matrix (Fin n) (Fin n) ℤ} (hUiU : Ui * U = 1) : IsPosGram ((qmat U)ᵀ * A * qmat U) :=
  isPosGram_conj U (fun v hv => by
    have := congrArg (Ui *ᵥ ·) hv
    simpa [Matrix.mulVec_mulVec, hUiU] using this) A hA

variable (K : Type) [Field K] [NumberField K]

/-- **The induction step of Theorem 7.5.1** (Kitaoka 1993, p. 242). If minimal tensors of $L \otimes (R_K, B_K)$ and
$M \otimes (R_K, B_K)$ split and every isometry between scalar extensions of positive lattices of rank $n$ is
integral, then so is every isometry $R_K L \cong R_K M$ for positive $L$, $M$ of rank $n + 1$. -/
theorem integral_step [IsTotallyReal K] {n : ℕ} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ} (hA : IsPosGram A)
    (hB : IsPosGram B) (hSA : SplitOK K A) (hSB : SplitOK K B)
    (ih : ∀ A' B' : Matrix (Fin n) (Fin n) ℚ, IsPosGram A' → IsPosGram B' →
      ∀ P' : Matrix (Fin n) (Fin n) (𝓞 K), IsScalarExtensionIsometry K A' B' P' →
        ∃ P₀ : Matrix (Fin n) (Fin n) ℤ, P' = icast K P₀)
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) (𝓞 K)} (hiso : IsScalarExtensionIsometry K A B P) :
    ∃ P₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ, P = icast K P₀ := by
  classical
  -- a minimal vector `xA` of `L` and its image `yB`, a minimal vector of `M`
  have hx0 : (Pi.single 0 1 : Fin (n + 1) → ℤ) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  obtain ⟨xA, hxA⟩ := Aux751.exists_isMinimalVector hA hx0
  obtain ⟨yB, hyB, hPx⟩ := first_col K hA hB hSA hSB hiso hxA
  -- unimodular completions
  obtain ⟨U, Ui, hUUi, hUiU, hU0⟩ := exists_unimodular xA (Aux751.exists_dual_of_minimal hA hxA)
  obtain ⟨V, Vi, hVVi, hViV, hV0⟩ := exists_unimodular yB (Aux751.exists_dual_of_minimal hB hyB)
  set A' := (qmat U)ᵀ * A * qmat U with hA'def
  set B' := (qmat V)ᵀ * B * qmat V with hB'def
  set P' := icast K Vi * P * icast K U with hP'def
  have hiso' : IsScalarExtensionIsometry K A' B' P' := iso_conj K hiso hUUi hVVi hViV
  have hA' : IsPosGram A' := isPosGram_conj_unimod hA hUiU
  have hB' : IsPosGram B' := isPosGram_conj_unimod hB hViV
  -- the first column of `P'` is `e₀`
  have hcol : ∀ i, P' i 0 = if i = 0 then 1 else 0 := by
    intro i
    have h1 : P' i 0 = ((icast K Vi * P) *ᵥ fun j => (xA j : 𝓞 K)) i := by
      simp [hP'def, Matrix.mul_apply, Matrix.mulVec, dotProduct, hU0]
    have h2 : Vi *ᵥ yB = fun i => (Vi * V) i 0 := by
      funext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hV0]
    rw [h1, ← Matrix.mulVec_mulVec, hPx, icast_mulVec, h2, hViV]
    by_cases hi : i = 0 <;> simp [Matrix.one_apply, hi]
  -- the Schur complement relation over `K`
  have hb : (B'.map (algebraMap ℚ K)) 0 0 ≠ 0 := by
    simp only [Matrix.map_apply]
    exact (map_ne_zero _).mpr (posGram_diag hB' 0).ne'
  obtain ⟨h00, h0l, hsch⟩ := schur_rel (A'.map (algebraMap ℚ K)) (B'.map (algebraMap ℚ K))
    (P'.map (algebraMap (𝓞 K) K)) hiso'.2 (fun i => by
      simp only [Matrix.map_apply, hcol i]; split_ifs <;> simp) hb
  set SA : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => A' i.succ j.succ - A' i.succ 0 * A' 0 j.succ / A' 0 0
    with hSAdef
  set SB : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => B' i.succ j.succ - B' i.succ 0 * B' 0 j.succ / B' 0 0
    with hSBdef
  set P'' : Matrix (Fin n) (Fin n) (𝓞 K) := P'.submatrix Fin.succ Fin.succ with hP''def
  have hiso'' : IsScalarExtensionIsometry K SA SB P'' := by
    refine ⟨by rw [hP''def, ← det_of_col P' hcol]; exact hiso'.1, Matrix.ext fun k l => ?_⟩
    have e := hsch k l
    simp only [Matrix.map_apply] at e
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, hSAdef,
      hSBdef, hP''def, Matrix.of_apply, map_sub, map_mul, map_div₀, Finset.sum_mul]
    rw [e, Finset.sum_comm]
  obtain ⟨Q0, hQ0⟩ := ih SA SB (schur_pos A' hA') (schur_pos B' hB') P'' hiso''
  have hP'' : ∀ i j : Fin n, P' i.succ j.succ = (Q0 i j : 𝓞 K) := by
    intro i j
    have := congrFun (congrFun hQ0 i) j
    simpa [hP''def] using this
  -- the first row of `P'` is integral
  have hrow : ∀ j : Fin n, ∃ z : ℤ, P' 0 j.succ = (z : 𝓞 K) := by
    intro j
    apply int_of_rat K (q := (A' 0 j.succ - ∑ i : Fin n, B' 0 i.succ * Q0 i j) / B' 0 0)
    have e := h0l j
    simp only [Matrix.map_apply, hP''] at e
    have hb' : algebraMap ℚ K (B' 0 0) ≠ 0 := by simpa using hb
    rw [map_div₀, map_sub, map_sum, eq_div_iff hb', e]
    simp only [map_mul, map_intCast]
    push_cast
    ring_nf
  choose z hz using hrow
  -- assemble
  let P0' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 z j) (fun i' => Fin.cases 0 (fun j' => Q0 i' j') j) i
  have hP'0 : P' = icast K P0' := by
    refine Matrix.ext fun i j => ?_
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · simp [P0', hcol, icast, Matrix.map_apply, Matrix.of_apply]
    · simp [P0', hz, icast, Matrix.map_apply, Matrix.of_apply]
    · simp [P0', hcol, icast, Matrix.map_apply, Matrix.of_apply]
    · simp [P0', hP'', icast, Matrix.map_apply, Matrix.of_apply]
  refine ⟨V * P0' * Ui, ?_⟩
  rw [icast_mul, icast_mul, ← hP'0, hP'def]
  calc P = (icast K V * icast K Vi) * P * (icast K U * icast K Ui) := by
        rw [← icast_mul, ← icast_mul, hVVi, hUUi, icast_one, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **The induction on the rank** (Kitaoka 1993, proof of Theorem 7.5.1, p. 242): if minimal tensors of
$L' \otimes (R_K, B_K)$ split for every positive lattice $L'$ of rank at most $N$, then every isometry
$R_K L \cong R_K M$ of positive lattices of rank $n \le N$ is an integer matrix, i.e. $\sigma(L) = M$. -/
theorem integral_of_splitOK [IsTotallyReal K] (N : ℕ)
    (hS : ∀ m ≤ N, ∀ A : Matrix (Fin m) (Fin m) ℚ, IsPosGram A → SplitOK K A) :
    ∀ n ≤ N, ∀ A B : Matrix (Fin n) (Fin n) ℚ, IsPosGram A → IsPosGram B →
      ∀ P : Matrix (Fin n) (Fin n) (𝓞 K), IsScalarExtensionIsometry K A B P →
        ∃ P₀ : Matrix (Fin n) (Fin n) ℤ, P = icast K P₀ := by
  intro n
  induction n with
  | zero => intro _ A B _ _ P _; exact ⟨0, Matrix.ext fun i => i.elim0⟩
  | succ n ih =>
    intro hn A B hA hB P hiso
    exact integral_step K hA hB (hS _ hn A hA) (hS _ hn B hB)
      (fun A' B' hA' hB' P' h' => ih (by omega) A' B' hA' hB' P' h') hiso

/-- **Kitaoka 1993, Theorem 7.5.1** (p. 242), the case "$(R_K, B_K)$ is of E-type", **unconditional**: let $K$ be
totally real with $(R_K, B_K)$, $B_K(x, y) = \operatorname{tr}_{K/\mathbb Q}(xy)$, of E-type. Then for positive
lattices $L = (\mathbb Z^n, A)$, $M = (\mathbb Z^n, B)$ every isometry $\sigma : R_K L \cong R_K M$ satisfies
$\sigma(L) = M$: its matrix $P$ has integer entries. -/
@[kb "kitaoka1993" "§7.5, Thm. 7.5.1, p. 242 ((R_K, B_K) of E-type)"]
theorem theorem751_of_isEType [IsTotallyReal K] (hE : IsEType (traceGram K)) (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℚ) (hA : IsPosGram A) (hB : IsPosGram B) (P : Matrix (Fin n) (Fin n) (𝓞 K))
    (hiso : IsScalarExtensionIsometry K A B P) : ∃ P₀ : Matrix (Fin n) (Fin n) ℤ, P = P₀.map (Int.cast : ℤ → 𝓞 K) :=
  integral_of_splitOK K n (fun _ _ A' hA' => splitOK_of_traceGram K hE A' hA') n le_rfl A B hA hB P hiso

/-- **Kitaoka 1993, Theorem 7.5.1** (p. 242), the case $\operatorname{rank} L \le 8$, **unconditional**: let $K$ be
totally real and $L = (\mathbb Z^n, A)$, $M = (\mathbb Z^n, B)$ positive lattices with $n \le 8$. Then every isometry
$\sigma : R_K L \cong R_K M$ satisfies $\sigma(L) = M$. (Kitaoka's hypothesis is $n < 43$, through Theorem 7.1.1;
here Theorem 7.1.1 is proved for $n \le 8$ by `theorem711_of_le_eight`.) -/
@[kb "kitaoka1993" "§7.5, Thm. 7.5.1, p. 242 (rank ≤ 8)"]
theorem theorem751_of_le_eight [IsTotallyReal K] (n : ℕ) (hn : n ≤ 8)
    (A B : Matrix (Fin n) (Fin n) ℚ) (hA : IsPosGram A) (hB : IsPosGram B) (P : Matrix (Fin n) (Fin n) (𝓞 K))
    (hiso : IsScalarExtensionIsometry K A B P) : ∃ P₀ : Matrix (Fin n) (Fin n) ℤ, P = P₀.map (Int.cast : ℤ → 𝓞 K) :=
  integral_of_splitOK K 8 (fun m hm A' hA' => splitOK_of_isEType K (theorem711_of_le_eight m hm A' hA'))
    n hn A B hA hB P hiso


/-- **Kitaoka 1993, Theorem 7.5.1 from Theorem 7.1.1** (p. 242): the stated `Theorem711` (every positive lattice of
rank $< 43$ is of E-type) implies `Theorem751` in full; the case "$(R_K, B_K)$ of E-type" needs no input
(`theorem751_of_isEType`). -/
@[kb "kitaoka1993" "§7.5, Thm. 7.5.1, p. 242 (from Thm. 7.1.1)"]
theorem theorem751_of_theorem711 (h711 : Theorem711) : Theorem751 := by
  intro K _ _ hK n A B hA hB hn P hiso
  rcases hn with hn | hE
  · exact integral_of_splitOK K 42 (fun m hm A' hA' => splitOK_of_isEType K (h711 m (by omega) A' hA'))
      n (by omega) A B hA hB P hiso
  · exact theorem751_of_isEType K hE n A B hA hB P hiso

/-- **Kitaoka 1993, Theorem 7.5.1 from Lemma 7.1.2** (pp. 193, 242): the stated Hermite bound `Lemma712`
($\mu_r < \sqrt r$ for $2 \le r < 43$) implies `Theorem751`. -/
@[kb "kitaoka1993" "§7.5, Thm. 7.5.1, p. 242 (from Lemma 7.1.2)"]
theorem theorem751_of_lemma712 (h : Lemma712) : Theorem751 :=
  theorem751_of_theorem711 (theorem711_of_lemma712 h)

end QuadFormsKB.Kitaoka.EType
