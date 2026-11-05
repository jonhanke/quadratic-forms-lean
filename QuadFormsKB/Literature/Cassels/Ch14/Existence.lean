/-
# Cassels, Chapter 14, §5: binary forms with prescribed local classes

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §5, pp. 343–345: the Corollary to Theorem 5.1 (an integral
binary form with prescribed $\mathbb Z_p$-classes) and Lemma 5.1 (a rational binary form with prescribed
$\mathbb Q_p$-classes, the case $n = 2$ of Ch. 6, Theorem 1.3).

*Conventions.* A binary form over a commutative ring $R$ is `QuadForm R 2`, $g = a x^2 + b xy + c y^2$; its
discriminant is $D = b^2 - 4ac = -\det H$, with $H$ the Hessian matrix $\begin{pmatrix} 2a & b \\ b & 2c\end{pmatrix}$
(Cassels, Ch. 14, (1.5): $D = -4d(f)$). Places are the primes $p$ and $\infty$, with $\mathbb Q_\infty = \mathbb R$.
The Hasse–Minkowski invariant (Cassels, Ch. 4, §1, p. 55) of a nondegenerate form over a field $K$ is
$c(g) = \prod_{i<j} (a_i, a_j)_K$ for a diagonalization $g \cong \langle a_0, \dots, a_{n-1} \rangle$ (`hasseC`, with a
chosen diagonalization; it does not depend on the choice over $\mathbb Q_p$, `hasseC_eq_of_isometric`).

*Proof route.* Cassels proves the Corollary to Theorem 5.1 from Theorem 5.1 (the image of $\mathcal G$ in
$\prod_p \mathcal G_p$) and deduces Lemma 5.1 from it, all without Dirichlet's theorem on primes in arithmetic
progressions (§7). The local groups $\mathcal G_p$ and Theorem 5.1 for general $D$ are not formalized; here the order
is reversed: Lemma 5.1 is proved from the existence of rationals with prescribed Hilbert symbols
(`Prescribed.exists_rat_prescribed_hilbert`, whose proof uses Dirichlet's theorem) and the classification of forms
over $\mathbb Q_p$ and $\mathbb R$; the Corollary then follows from Lemma 5.1 and the existence of genera (Ch. 9,
Theorem 1.2, `Siegel.exists_form_of_local_forms`).
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec5Exist
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.LocalGlobal.PrescribedSymbols
import QuadFormsKB.Literature.LocalGlobal.FieldGeneral
import QuadFormsKB.Literature.Cassels.Ch14.Group
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationNF

namespace QuadFormsKB.Composition

open QuadForm Siegel

/-- **The Hasse–Minkowski invariant** $c(g) = \prod_{0 \le i < j < n} (a_i, a_j)_K$ of a nondegenerate form $g$ over a
field $K$ of characteristic $0$ (Cassels, Ch. 4, §1, p. 55), computed from a chosen diagonalization
$g \cong \langle a_0, \dots, a_{n-1} \rangle$ over $K$ (`FieldGen.exists_isometric_diag`); $(\cdot,\cdot)_K$ is the
Hilbert symbol `hilbertSymbol K`. For a degenerate $g$ the value is $1$ (never used). Over $\mathbb Q_p$ the value does
not depend on the diagonalization (`hasseC_eq_of_isometric`, Cassels, Ch. 4, Lemma 2.2). -/
@[kb "cassels1978" "Ch. 4, §1, p. 55 (the Hasse–Minkowski invariant c_p)"]
noncomputable def hasseC {K : Type*} [Field K] [CharZero K] {n : ℕ} (g : QuadForm K n) : ℤ := by
  classical
  exact if hg : g.Nondegenerate then PadicClass.hasseVec (Classical.choose (FieldGen.exists_isometric_diag g hg))
    else 1

/-- **The Hasse–Minkowski invariant over $\mathbb Q_p$ is an isometry invariant** (Cassels, Ch. 4, Lemma 2.2, p. 57):
it may be computed from any diagonalization. -/
theorem hasseC_eq_of_isometric (p : ℕ) [Fact p.Prime] {n : ℕ} {g : QuadForm ℚ_[p] n} (hg : g.Nondegenerate)
    {a : Fin n → ℚ_[p]} (ha : ∀ i, a i ≠ 0) (h : g.IsometricIn ℚ_[p] (QuadForm.diag a)) :
    hasseC g = PadicClass.hasseVec a := by
  classical
  have hex := FieldGen.exists_isometric_diag g hg
  unfold hasseC
  simp only [hg, ↓reduceDIte]
  obtain ⟨hb0, hbiso⟩ := Classical.choose_spec hex
  exact PadicClass.hasseVec_eq_of_isometric (PadicClass.localHilbertField_padic p) n _ a hb0 ha
    (QuadForm.isometricIn_trans _ (QuadForm.isometricIn_symm _ hbiso) h)

/-- The Hasse–Minkowski invariants $c_p(g_p)$ of a family of forms $g_p$ over $\mathbb Q_p$, indexed by the primes. -/
noncomputable def hasseAt {n : ℕ} (g : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℚ_[p] n) (p : Nat.Primes) : ℤ :=
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  hasseC (g p)

/-! ### Local helpers for Lemma 5.1 -/

/-- $c(g) = \pm 1$. -/
theorem hasseC_pm {K : Type*} [Field K] [CharZero K] {n : ℕ} (g : QuadForm K n) :
    hasseC g = 1 ∨ hasseC g = -1 := by
  classical
  unfold hasseC
  split_ifs
  · exact PadicClass.hasseVec_pm _
  · exact Or.inl rfl

/-- $(\alpha, -D/(4\alpha))_K = (\alpha, D)_K$, given bimultiplicativity of the symbol on $K^\times$. -/
theorem hs_normal_form {K : Type*} [Field K] [CharZero K]
    (hml : ∀ a a' b : K, a ≠ 0 → a' ≠ 0 → b ≠ 0 →
      hilbertSymbol K (a * a') b = hilbertSymbol K a b * hilbertSymbol K a' b)
    {α D : K} (hα : α ≠ 0) (hD : D ≠ 0) :
    hilbertSymbol K α (-D / (4 * α)) = hilbertSymbol K α D := by
  have hmr : ∀ a b b' : K, a ≠ 0 → b ≠ 0 → b' ≠ 0 →
      hilbertSymbol K a (b * b') = hilbertSymbol K a b * hilbertSymbol K a b' := by
    intro a b b' ha hb hb'
    rw [hilbertSymbol_comm, hml _ _ _ hb hb' ha, hilbertSymbol_comm K b, hilbertSymbol_comm K b']
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hi : ((2 * α)⁻¹) ≠ 0 := inv_ne_zero (mul_ne_zero h2 hα)
  have e : -D / (4 * α) = (D * (-α)) * ((2 * α)⁻¹) ^ 2 := by field_simp; ring
  rw [e, hmr _ _ _ hα (mul_ne_zero hD (neg_ne_zero.mpr hα)) (pow_ne_zero 2 hi),
    hmr _ _ _ hα hD (neg_ne_zero.mpr hα), hilbertSymbol_self_neg, PadicClass.hs_sq _ _ hi]
  ring

/-- If $g \cong \langle a_0, a_1 \rangle$ (all $a_i \ne 0$) and $D = -\det H$, then
$g \cong \langle a_0, -D/(4a_0) \rangle$. -/
theorem normal_form_of_diag {K : Type*} [Field K] [CharZero K] {g : QuadForm K 2}
    {D : K} (hD : -g.hessian.det = D) {a : Fin 2 → K} (ha : ∀ i, a i ≠ 0)
    (hga : g.IsometricIn K (QuadForm.diag a)) :
    g.IsometricIn K (QuadForm.diag ![a 0, -D / (4 * a 0)]) := by
  obtain ⟨P, hP, hPe⟩ := hga
  have hdet := congrArg Matrix.det (PadicClass.transpose_mul_hessian_mul hPe)
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hdiag : (QuadForm.diag a).hessian.det = 4 * a 0 * a 1 := by
    rw [Binary.hessian_det_two]; simp [QuadForm.diag]
  rw [hdiag] at hdet
  have hs0 : P.det ≠ 0 := hP.ne_zero
  have h0 := ha 0
  have h1 := ha 1
  have hDe : D = -(4 * a 0 * a 1) / P.det ^ 2 := by
    rw [← hD]; field_simp; linear_combination (-1 : K) * hdet
  refine QuadForm.isometricIn_trans _ ⟨P, hP, hPe⟩ ?_
  refine LocalClassNF.isometricIn_diag_of_sq ![1, P.det⁻¹] ?_ ?_
  · intro i; fin_cases i
    · simp
    · simpa using hs0
  · intro i; fin_cases i
    · simp
    · simp only [hDe]; field_simp; simp; ring

/-- A nondegenerate binary form over a field is isometric to $\langle \alpha, -D/(4\alpha) \rangle$ for some
$\alpha \ne 0$, where $D = -\det H$. -/
theorem exists_normal_form {K : Type*} [Field K] [CharZero K] {g : QuadForm K 2} (hg : g.Nondegenerate)
    {D : K} (hD : -g.hessian.det = D) :
    ∃ α : K, α ≠ 0 ∧ g.IsometricIn K (QuadForm.diag ![α, -D / (4 * α)]) := by
  obtain ⟨a, ha, hga⟩ := FieldGen.exists_isometric_diag g hg
  exact ⟨a 0, ha 0, normal_form_of_diag hD ha hga⟩

/-- A nondegenerate form has $-\det H \neq 0$. -/
theorem nondeg_of_det {K : Type*} [Field K] {g : QuadForm K 2} {D : K} (hD : D ≠ 0)
    (hg : -g.hessian.det = D) : g.Nondegenerate := by
  change g.hessian.det ≠ 0
  intro h
  rw [h] at hg
  exact hD (by simpa using hg.symm)

theorem hne_diag_two {K : Type*} [Field K] [CharZero K] {D : K} (hD : D ≠ 0) {x : K} (hx : x ≠ 0) :
    ∀ i, (![x, -D / (4 * x)] : Fin 2 → K) i ≠ 0 := by
  intro i; fin_cases i
  · simpa using hx
  · have : (4 : K) ≠ 0 := by norm_num
    simp [hD, hx, this]

/-- **Local classification at $p$:** a binary form over $\mathbb Q_p$ with $-\det H = D \ne 0$ is isometric to
$\langle x, -D/(4x)\rangle$ exactly for those $x$ with $(D, x)_p = c(g)$, and such an $x$ exists. -/
theorem local_class_padic (p : ℕ) [Fact p.Prime] {g : QuadForm ℚ_[p] 2} {D : ℚ_[p]} (hD : D ≠ 0)
    (hg : -g.hessian.det = D) :
    (∃ α : ℚ_[p], α ≠ 0 ∧ hilbertSymbol ℚ_[p] D α = hasseC g) ∧
    ∀ x : ℚ_[p], x ≠ 0 → hilbertSymbol ℚ_[p] D x = hasseC g →
      g.IsometricIn ℚ_[p] (QuadForm.diag ![x, -D / (4 * x)]) := by
  have hnd : g.Nondegenerate := nondeg_of_det hD hg
  obtain ⟨α, hα, hiso⟩ := exists_normal_form hnd hg
  have hK := PadicClass.localHilbertField_padic p
  have hC : hasseC g = hilbertSymbol ℚ_[p] α D := by
    rw [hasseC_eq_of_isometric p hnd (hne_diag_two hD hα) hiso, PadicClass.hasseVec_two,
      hs_normal_form hK.mul_left hα hD]
  refine ⟨⟨α, hα, by rw [hC, hilbertSymbol_comm]⟩, fun x hx hxe => ?_⟩
  refine QuadForm.isometricIn_trans _ hiso (PadicClass.isometric_of_invariants hK 2 _ _ (hne_diag_two hD hα)
    (hne_diag_two hD hx) ⟨1, one_ne_zero, ?_⟩ ?_)
  · simp only [Fin.prod_univ_two]
    have : (4 : ℚ_[p]) ≠ 0 := by norm_num
    simp; field_simp
  · rw [PadicClass.hasseVec_two, PadicClass.hasseVec_two, hs_normal_form hK.mul_left hα hD,
      hs_normal_form hK.mul_left hx hD, ← hC, ← hxe]
    exact hilbertSymbol_comm _ _ _

/-- Isometric real diagonal binary forms have the same Hasse invariant. -/
theorem real_hasse_eq {a b : Fin 2 → ℝ} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : (QuadForm.diag a).IsometricIn ℝ (QuadForm.diag b)) :
    PadicClass.hasseVec a = PadicClass.hasseVec b := by
  have hn := (LocalClassNF.isometric_real_vec_iff a b ha hb).mp h
  simp only [HasseIsoNF.negCountR, Fin.sum_univ_two] at hn
  rw [PadicClass.eq_vec_two a, PadicClass.eq_vec_two b, PadicClass.hasseVec_two, PadicClass.hasseVec_two,
    HasseIsoNF.hilbertSymbol_real_eq _ _ (ha 0) (ha 1), HasseIsoNF.hilbertSymbol_real_eq _ _ (hb 0) (hb 1)]
  by_cases h0 : a 0 < 0 <;> by_cases h1 : a 1 < 0 <;> by_cases h2 : b 0 < 0 <;> by_cases h3 : b 1 < 0 <;>
    simp [h0, h1, h2, h3] at hn ⊢

/-- The number of negative entries of $\langle \alpha, -D/(4\alpha)\rangle$ over $\mathbb R$. -/
theorem negCount_two {D α : ℝ} (hα : α ≠ 0) :
    HasseIsoNF.negCountR ![α, -D / (4 * α)] = (if α < 0 then 1 else 0) + (if 0 < D * α then 1 else 0) := by
  have e : -D / (4 * α) < 0 ↔ 0 < D * α := by
    have e1 : -D / (4 * α) = -(D * α) / (4 * α ^ 2) := by field_simp
    have h4 : 0 < 4 * α ^ 2 := by positivity
    rw [e1, div_lt_iff₀ h4]
    simp
  simp only [HasseIsoNF.negCountR, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e]
  congr

/-- **Local classification at $\infty$** (the analogue of `local_class_padic` over $\mathbb R$). -/
theorem local_class_real {g : QuadForm ℝ 2} {D : ℝ} (hD : D ≠ 0) (hg : -g.hessian.det = D) :
    (∃ α : ℝ, α ≠ 0 ∧ hilbertSymbol ℝ D α = hasseC g) ∧
    ∀ x : ℝ, x ≠ 0 → hilbertSymbol ℝ D x = hasseC g →
      g.IsometricIn ℝ (QuadForm.diag ![x, -D / (4 * x)]) := by
  classical
  have hnd : g.Nondegenerate := nondeg_of_det hD hg
  obtain ⟨α, hα, hiso⟩ := exists_normal_form hnd hg
  have hml := HilbertLocal.hilbertSymbol_real_mul_left
  have hC : hasseC g = hilbertSymbol ℝ α D := by
    have hex := FieldGen.exists_isometric_diag g hnd
    unfold hasseC
    simp only [hnd, ↓reduceDIte]
    obtain ⟨hb0, hbiso⟩ := Classical.choose_spec hex
    rw [real_hasse_eq hb0 (hne_diag_two hD hα)
      (QuadForm.isometricIn_trans _ (QuadForm.isometricIn_symm _ hbiso) hiso), PadicClass.hasseVec_two,
      hs_normal_form hml hα hD]
  refine ⟨⟨α, hα, by rw [hC, hilbertSymbol_comm]⟩, fun x hx hxe => ?_⟩
  refine QuadForm.isometricIn_trans _ hiso
    ((LocalClassNF.isometric_real_vec_iff _ _ (hne_diag_two hD hα) (hne_diag_two hD hx)).mpr ?_)
  have heq : hilbertSymbol ℝ D α = hilbertSymbol ℝ D x := by
    rw [hxe, hC, hilbertSymbol_comm]
  rw [HasseIsoNF.hilbertSymbol_real_eq _ _ hD hα, HasseIsoNF.hilbertSymbol_real_eq _ _ hD hx] at heq
  rw [negCount_two hα, negCount_two hx]
  rcases hD.lt_or_gt with h0 | h0 <;> rcases hα.lt_or_gt with h1 | h1 <;> rcases hx.lt_or_gt with h2 | h2 <;>
    simp_all [mul_pos_iff, not_lt_of_gt]

/-- Mapping a diagonal form along a ring homomorphism. -/
theorem map_diag {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (a : Fin n → R) :
    (QuadForm.diag a).map f = QuadForm.diag (f ∘ a) := by
  apply QuadForm.ext
  simp [QuadForm.map, QuadForm.diag, Matrix.diagonal_map]

/-- **Cassels, Ch. 14, Lemma 5.1** (p. 345): *let $D \in \mathbb Q^\times$. For all $p$ including $\infty$ let
$g_p(x, y)$ be a $\mathbb Q_p$-form of discriminant $D$. Suppose that the Hasse–Minkowski symbol $c(g_p)$ is $+1$ for
all except finitely many $p$ and that $\prod_{p \text{ incl. } \infty} c(g_p) = 1$. Then there is a $\mathbb Q$-form
of discriminant $D$ which is equivalent to $g_p$ over $\mathbb Q_p$ for each $p$.* Here $g_p$ (`g p`) is a form over
$\mathbb Q_p$ for each prime $p$ and $g_\infty$ (`gInf`) a form over $\mathbb R$; the discriminant of a binary form is
$-\det H$ (see the module docstring). This is the case $n = 2$ of Ch. 6, Theorem 1.3. -/
@[kb "cassels1978" "Ch. 14, Lemma 5.1, p. 345"]
theorem exists_rat_form_of_local (D : ℚ) (hD : D ≠ 0) (g : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℚ_[p] 2)
    (hg : ∀ (p : ℕ) [Fact p.Prime], -(g p).hessian.det = (D : ℚ_[p])) (gInf : QuadForm ℝ 2)
    (hgInf : -gInf.hessian.det = (D : ℝ)) (hfin : {p : Nat.Primes | hasseAt g p ≠ 1}.Finite)
    (hprod : (∏ᶠ p : Nat.Primes, hasseAt g p) * hasseC gInf = 1) :
    ∃ G : QuadForm ℚ 2, -G.hessian.det = D ∧
      (∀ (p : ℕ) [Fact p.Prime], IsometricGL (G.map (Rat.castHom ℚ_[p])) (g p)) ∧
      IsometricGL (G.map (Rat.castHom ℝ)) gInf := by
  classical
  let ε : Fin 1 → RatPlace → ℤ := fun _ v =>
    match v with
    | .infinite => hasseC gInf
    | .finite p => hasseAt g p
  have hεinf : ∀ i, ε i .infinite = hasseC gInf := fun _ => rfl
  have hεfin : ∀ i (p : Nat.Primes), ε i (.finite p) = hasseAt g p := fun _ _ => rfl
  have hε : ∀ i v, ε i v = 1 ∨ ε i v = -1 := by
    intro i v
    cases v
    · rw [hεinf i]; exact hasseC_pm _
    · rw [hεfin i]; exact hasseC_pm _
  have h1 : {v : RatPlace | ∃ i, ε i v = -1}.Finite := by
    refine ((hfin.image RatPlace.finite).insert RatPlace.infinite).subset ?_
    rintro (_ | p) ⟨i, hi⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨p, ?_, rfl⟩
      rw [hεfin i] at hi
      show hasseAt g p ≠ 1
      rw [hi]; norm_num
  have h2 : ∀ i, Even {v : RatPlace | ε i v = -1}.ncard := by
    intro i
    set T : Finset Nat.Primes := hfin.toFinset.filter (fun p => hasseAt g p = -1) with hT
    have hprodT : ∏ᶠ p : Nat.Primes, hasseAt g p = (-1) ^ T.card := by
      rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by intro p hp; simpa using hp)]
      have : ∀ p ∈ hfin.toFinset, hasseAt g p = (-1) ^ (if hasseAt g p = -1 then 1 else 0) := by
        intro p _
        rcases hasseC_pm (g p) with h | h
        · have h' : hasseAt g p = 1 := h
          rw [h']; simp
        · have h' : hasseAt g p = -1 := h
          simp [h']
      rw [Finset.prod_congr rfl this, Finset.prod_pow_eq_pow_sum, hT, Finset.card_filter]
    have hmemT : ∀ p : Nat.Primes, p ∈ T ↔ hasseAt g p = -1 := by
      intro p
      rw [hT, Finset.mem_filter, Set.Finite.mem_toFinset]
      constructor
      · exact fun h => h.2
      · intro h; refine ⟨?_, h⟩; show hasseAt g p ≠ 1; rw [h]; norm_num
    have hinj : Function.Injective RatPlace.finite := fun a b h => by injection h
    have hneg1 : ((-1 : ℤ)) ≠ 1 := by norm_num
    rcases hasseC_pm gInf with hc | hc
    · have hset : {v : RatPlace | ε i v = -1} = RatPlace.finite '' (T : Set Nat.Primes) := by
        ext v
        cases v with
        | infinite => simp [hεinf, hc]
        | finite p => simp [hεfin, hmemT]
      rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]
      rw [hprodT, hc, mul_one] at hprod
      exact (neg_one_pow_eq_one_iff_even hneg1).mp hprod
    · have hset : {v : RatPlace | ε i v = -1} = insert RatPlace.infinite (RatPlace.finite '' (T : Set Nat.Primes)) := by
        ext v
        cases v with
        | infinite => simp [hεinf, hc]
        | finite p => simp [hεfin, hmemT]
      rw [hset, Set.ncard_insert_of_notMem (by simp) ((T.finite_toSet).image _),
        Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]
      rw [hprodT, hc] at hprod
      have : (-1 : ℤ) ^ (T.card + 1) = 1 := by rw [pow_succ]; exact hprod
      exact (neg_one_pow_eq_one_iff_even hneg1).mp this
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have h3 : ∀ v : RatPlace, v.atPlace fun K _ _ =>
      ∃ x : K, x ≠ 0 ∧ ∀ i, hilbertSymbol K (algebraMap ℚ K ((fun _ => D) i)) x = ε i v := by
    intro v
    cases v with
    | infinite =>
      obtain ⟨⟨α, hα, hαe⟩, -⟩ := local_class_real hDr hgInf
      exact ⟨α, hα, fun i => by simpa [hεinf] using hαe⟩
    | finite p =>
      have : Fact (p : ℕ).Prime := ⟨p.2⟩
      have hDp : (D : ℚ_[p]) ≠ 0 := by exact_mod_cast hD
      obtain ⟨⟨α, hα, hαe⟩, -⟩ := local_class_padic p (g := g p) hDp (hg p)
      exact ⟨α, hα, fun i => by simpa [hεfin, hasseAt] using hαe⟩
  obtain ⟨x, hx0, hx⟩ := Prescribed.exists_rat_prescribed_hilbert (fun _ : Fin 1 => D) (fun _ => hD) ε hε h1 h2 h3
  have hxD : -D / (4 * x) ≠ 0 := by
    have : (4 : ℚ) ≠ 0 := by norm_num
    simp [hD, hx0, this]
  refine ⟨QuadForm.diag ![x, -D / (4 * x)], ?_, ?_, ?_⟩
  · rw [Binary.hessian_det_two]
    simp [QuadForm.diag]
    field_simp
  · intro p hp
    have hDp : (D : ℚ_[p]) ≠ 0 := by exact_mod_cast hD
    obtain ⟨-, hiso⟩ := local_class_padic p (g := g p) hDp (hg p)
    have hxp : (x : ℚ_[p]) ≠ 0 := by exact_mod_cast hx0
    have hh := (hx 0 (.finite ⟨p, hp.out⟩)).trans (hεfin 0 ⟨p, hp.out⟩)
    have hiso' := hiso (x : ℚ_[p]) hxp (by simpa [RatPlace.hilbert, hasseAt] using hh)
    rw [isometricGL_iff_isometricIn]
    have hm : (QuadForm.diag ![x, -D / (4 * x)]).map (Rat.castHom ℚ_[p]) =
        QuadForm.diag ![(x : ℚ_[p]), -(D : ℚ_[p]) / (4 * (x : ℚ_[p]))] := by
      rw [map_diag]
      congr 1
      funext i; fin_cases i <;> simp
    rw [hm]
    exact QuadForm.isometricIn_symm _ hiso'
  · have hxr : (x : ℝ) ≠ 0 := by exact_mod_cast hx0
    obtain ⟨-, hiso⟩ := local_class_real hDr hgInf
    have hh := (hx 0 .infinite).trans (hεinf 0)
    have hiso' := hiso (x : ℝ) hxr (by simpa [RatPlace.hilbert] using hh)
    rw [isometricGL_iff_isometricIn]
    have hm : (QuadForm.diag ![x, -D / (4 * x)]).map (Rat.castHom ℝ) =
        QuadForm.diag ![(x : ℝ), -(D : ℝ) / (4 * (x : ℝ))] := by
      rw [map_diag]
      congr 1
      funext i; fin_cases i <;> simp
    rw [hm]
    exact QuadForm.isometricIn_symm _ hiso'

/-- The value of a binary form on a vector $(x, y)$. -/
theorem eval_two {R : Type*} [CommRing R] (F : QuadForm R 2) (x y : R) :
    F.eval ![x, y] = F.coeff 0 0 * x ^ 2 + F.coeff 0 1 * x * y + F.coeff 1 1 * y ^ 2 := by
  have h10 : F.coeff 1 0 = 0 := F.upper (show (0 : Fin 2) < 1 by decide)
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two]
  ring


/-- **A primitive $\mathbb Z_p$-integral binary form**: $g = a x^2 + bxy + cy^2$ with $a, b, c \in \mathbb Z_p$ not all
divisible by $p$ (Cassels, Ch. 14, §1, p. 331, over $\mathbb Z_p$). -/
def IsPrimitiveZp {p : ℕ} [Fact p.Prime] (g : QuadForm ℤ_[p] 2) : Prop :=
  IsUnit (g.coeff 0 0) ∨ IsUnit (g.coeff 0 1) ∨ IsUnit (g.coeff 1 1)

/-- A primitive binary form over $\mathbb Z_p$ takes a unit value. -/
theorem exists_unit_value {p : ℕ} [Fact p.Prime] {f : QuadForm ℤ_[p] 2} (hf : IsPrimitiveZp f) :
    ∃ v : Fin 2 → ℤ_[p], IsUnit (f.eval v) := by
  by_cases ha : IsUnit (f.coeff 0 0)
  · refine ⟨![1, 0], ?_⟩
    rw [eval_two]; simpa using ha
  by_cases hc : IsUnit (f.coeff 1 1)
  · refine ⟨![0, 1], ?_⟩
    rw [eval_two]; simpa using hc
  have hb : IsUnit (f.coeff 0 1) := by
    rcases hf with h | h | h
    · exact absurd h ha
    · exact h
    · exact absurd h hc
  refine ⟨![1, 1], ?_⟩
  rw [eval_two]
  simp only [one_pow, mul_one]
  by_contra hn
  have hac : ¬ IsUnit (f.coeff 0 0 + f.coeff 1 1) := fun h =>
    (IsLocalRing.isUnit_or_isUnit_of_isUnit_add h).elim ha hc
  have : IsUnit ((f.coeff 0 0 + f.coeff 0 1 + f.coeff 1 1) + (-(f.coeff 0 0 + f.coeff 1 1))) := by
    rw [show (f.coeff 0 0 + f.coeff 0 1 + f.coeff 1 1) + (-(f.coeff 0 0 + f.coeff 1 1)) = f.coeff 0 1 by ring]
    exact hb
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h | h
  · exact hn h
  · exact hac (by simpa using h.neg)

/-- **Almost all local invariants are $1$:** for a family of primitive $\mathbb Z_p$-integral binary forms $f_p$ of
discriminant $D \ne 0$, $c_p(f_p) = 1$ for every $p \nmid 2D$ (Cassels, Ch. 14, Lemma 3.1 (i), p. 339: such $f_p$ is
$\mathbb Z_p$-equivalent to $x^2 - \tfrac14 D y^2$). -/
theorem hasseAt_eq_one_of_not_dvd {D : ℤ} (f : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℤ_[p] 2)
    (hprim : ∀ (p : ℕ) [Fact p.Prime], IsPrimitiveZp (f p))
    (hf : ∀ (p : ℕ) [Fact p.Prime], -(f p).hessian.det = (D : ℤ_[p])) (p : Nat.Primes)
    (hp : ¬ ((p : ℕ) : ℤ) ∣ 2 * D) : hasseAt (fun q _ => (f q).map PadicInt.Coe.ringHom) p = 1 := by
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  have hp2 : (p : ℕ) ≠ 2 := by
    intro h; apply hp; rw [h]; exact ⟨D, by push_cast; ring⟩
  have hpD : ¬ ((p : ℕ) : ℤ) ∣ D := fun h => hp (Dvd.dvd.mul_left h 2)
  have hDu : IsUnit (D : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hpD ?_)
    exact (PadicInt.norm_int_lt_one_iff_dvd D).mp h
  set g : QuadForm ℚ_[p] 2 := (f p).map PadicInt.Coe.ringHom with hgdef
  have hcoe : ∀ i j, g.coeff i j = (((f p).coeff i j : ℤ_[p]) : ℚ_[p]) := fun i j => rfl
  have hD0 : ((D : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    exact fun h => hDu.ne_zero (PadicInt.coe_eq_zero.mp h)
  have hg : -g.hessian.det = ((D : ℤ_[p]) : ℚ_[p]) := by
    have h := hf p
    rw [Binary.hessian_det_two] at h ⊢
    have h2 := congrArg PadicInt.Coe.ringHom h
    simp only [map_neg, map_sub, map_mul, map_pow, map_ofNat] at h2
    simp only [hcoe]
    exact h2
  have hnd : g.Nondegenerate := nondeg_of_det hD0 hg
  obtain ⟨v, hv⟩ := exists_unit_value (hprim p)
  set u : ℤ_[p] := (f p).eval v with hu
  have hu0 : (u : ℚ_[p]) ≠ 0 := fun h => hv.ne_zero (PadicInt.coe_eq_zero.mp h)
  have hrep : g.RepresentsIn ℚ_[p] (u : ℚ_[p]) := by
    refine ⟨fun i => (v i : ℚ_[p]), ?_⟩
    have hv2 : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    have e1 : g.evalIn ℚ_[p] (fun i => (v i : ℚ_[p])) = g.eval ![(v 0 : ℚ_[p]), (v 1 : ℚ_[p])] := by
      congr 1; funext i; fin_cases i <;> rfl
    rw [e1, eval_two]
    simp only [hcoe, Algebra.algebraMap_self, RingHom.id_apply, hu]
    conv_rhs => rw [hv2, eval_two]
    push_cast; ring
  obtain ⟨α, hα, hiso⟩ := QuadForm.exists_isometric_diag_cons hnd hu0 hrep
  have hiso2 : g.IsometricIn ℚ_[p] (QuadForm.diag ![(u : ℚ_[p]), -((D : ℤ_[p]) : ℚ_[p]) / (4 * (u : ℚ_[p]))]) := by
    have := normal_form_of_diag hg (a := Fin.cons (u : ℚ_[p]) α) (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hu0
      · simpa using hα j) hiso
    simpa using this
  have hK := PadicClass.localHilbertField_padic (p : ℕ)
  show hasseC g = 1
  rw [hasseC_eq_of_isometric (p : ℕ) hnd (hne_diag_two hD0 hu0) hiso2, PadicClass.hasseVec_two,
    hs_normal_form hK.mul_left hu0 hD0]
  have := HilbertLocal.hilbertSymbol_units hp2 hv.unit hDu.unit
  simpa using this

/-- Passing a form over $\mathbb Z_p$ to $\mathbb Q_p$ preserves $-\det H = D$. -/
theorem neg_det_map {p : ℕ} [Fact p.Prime] {F : QuadForm ℤ_[p] 2} {D : ℤ}
    (h : -F.hessian.det = (D : ℤ_[p])) :
    -(F.map PadicInt.Coe.ringHom).hessian.det = (D : ℚ_[p]) := by
  rw [Binary.hessian_det_two] at h ⊢
  have h2 := congrArg PadicInt.Coe.ringHom h
  simp only [map_neg, map_sub, map_mul, map_pow, map_ofNat, map_intCast] at h2
  exact h2

/-- **Discriminant transformation:** if $F(g\mathbf x) = f(\mathbf x)$ then
$b_f^2 - 4a_fc_f = (\det g)^2 (b_F^2 - 4a_Fc_F)$. -/
theorem disc_transform {R : Type*} [CommRing R] (Fm f : QuadForm R 2) (g : GL (Fin 2) R)
    (h : ∀ x, Fm.eval (Matrix.mulVec g.val x) = f.eval x) :
    f.coeff 0 1 ^ 2 - 4 * f.coeff 0 0 * f.coeff 1 1 =
      (g.val.det) ^ 2 * (Fm.coeff 0 1 ^ 2 - 4 * Fm.coeff 0 0 * Fm.coeff 1 1) := by
  have hv : ∀ x y : R, Matrix.mulVec g.val ![x, y] =
      ![g.val 0 0 * x + g.val 0 1 * y, g.val 1 0 * x + g.val 1 1 * y] := by
    intro x y; ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e0 := h ![1, 0]
  have e1 := h ![0, 1]
  have e2 := h ![1, 1]
  rw [hv, eval_two, eval_two] at e0 e1 e2
  rw [Matrix.det_fin_two]
  have ha : f.coeff 0 0 = Fm.coeff 0 0 * g.val 0 0 ^ 2 + Fm.coeff 0 1 * g.val 0 0 * g.val 1 0
      + Fm.coeff 1 1 * g.val 1 0 ^ 2 := by linear_combination (-1 : R) * e0
  have hc : f.coeff 1 1 = Fm.coeff 0 0 * g.val 0 1 ^ 2 + Fm.coeff 0 1 * g.val 0 1 * g.val 1 1
      + Fm.coeff 1 1 * g.val 1 1 ^ 2 := by linear_combination (-1 : R) * e1
  have hb : f.coeff 0 1 = Fm.coeff 0 0 * (2 * g.val 0 0 * g.val 0 1) + Fm.coeff 0 1 *
      (g.val 0 0 * g.val 1 1 + g.val 0 1 * g.val 1 0) + Fm.coeff 1 1 * (2 * g.val 1 0 * g.val 1 1) := by
    linear_combination (-1 : R) * (e2 - e0 - e1)
  rw [ha, hb, hc]
  ring

/-- If integers $x, y$ differ by a $\mathbb Z_p$-unit factor for every $p$, then $|x| = |y|$. -/
theorem natAbs_eq_of_unit_mul {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ (p : ℕ) [Fact p.Prime], ∃ u : ℤ_[p], IsUnit u ∧ (y : ℤ_[p]) = u * x) :
    x.natAbs = y.natAbs := by
  refine (Nat.eq_iff_prime_padicValNat_eq _ _ (Int.natAbs_ne_zero.mpr hx)
    (Int.natAbs_ne_zero.mpr hy)).mpr fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  have key : ∀ n : ℕ, p ^ n ∣ x.natAbs ↔ p ^ n ∣ y.natAbs := by
    intro n
    rw [← Int.natCast_dvd, ← Int.natCast_dvd, Nat.cast_pow,
      ← PadicInt.norm_int_le_pow_iff_dvd, ← PadicInt.norm_int_le_pow_iff_dvd]
    obtain ⟨u, hu, e⟩ := h p
    rw [e, norm_mul, PadicInt.isUnit_iff.mp hu, one_mul]
  have hx' : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx
  have hy' : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy
  apply le_antisymm
  · exact (padicValNat_dvd_iff_le hy').mp ((key _).mp pow_padicValNat_dvd)
  · exact (padicValNat_dvd_iff_le hx').mp ((key _).mpr pow_padicValNat_dvd)

/-- A global integral binary form that is $\mathbb Z_p$-equivalent to a primitive form for every $p$ is primitive. -/
theorem isPrimitive_of_local (F : BinQF) (f : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℤ_[p] 2)
    (hprim : ∀ (p : ℕ) [Fact p.Prime], IsPrimitiveZp (f p))
    (hF : ∀ (p : ℕ) [Fact p.Prime], IsometricGL (F.map (Int.castRingHom ℤ_[p])) (f p)) :
    F.IsPrimitive := by
  intro d ha hb hc
  by_contra hd
  rw [Int.isUnit_iff_natAbs_eq] at hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  have : Fact p.Prime := ⟨hp⟩
  have hpd' : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hpd
  have hdiv : ∀ w : Fin 2 → ℤ_[p], (p : ℤ_[p]) ∣ (F.map (Int.castRingHom ℤ_[p])).eval w := by
    intro w
    have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
    rw [hw, eval_two]
    have h1 : ∀ z : ℤ, z ∈ ({F.coeff 0 0, F.coeff 0 1, F.coeff 1 1} : Set ℤ) → (p : ℤ_[p]) ∣ (z : ℤ_[p]) := by
      intro z hz
      have : (p : ℤ) ∣ z := by
        rcases hz with rfl | rfl | rfl
        · exact hpd'.trans ha
        · exact hpd'.trans hb
        · exact hpd'.trans hc
      obtain ⟨k, hk⟩ := this
      exact ⟨k, by rw [hk]; push_cast; ring⟩
    have c0 := h1 _ (Or.inl rfl)
    have c1 := h1 _ (Or.inr (Or.inl rfl))
    have c2 := h1 _ (Or.inr (Or.inr rfl))
    show (p : ℤ_[p]) ∣ (F.coeff 0 0 : ℤ_[p]) * w 0 ^ 2 + (F.coeff 0 1 : ℤ_[p]) * w 0 * w 1 +
      (F.coeff 1 1 : ℤ_[p]) * w 1 ^ 2
    exact dvd_add (dvd_add (c0.mul_right _) ((c1.mul_right _).mul_right _)) (c2.mul_right _)
  obtain ⟨g, hg⟩ := hF p
  have hd' : ∀ w : Fin 2 → ℤ_[p], (p : ℤ_[p]) ∣ (f p).eval w := by
    intro w; rw [← hg]; exact hdiv _
  have a0 := hd' ![1, 0]
  have a1 := hd' ![0, 1]
  have a2 := hd' ![1, 1]
  rw [eval_two] at a0 a1 a2
  have hA : (p : ℤ_[p]) ∣ (f p).coeff 0 0 := by simpa using a0
  have hC : (p : ℤ_[p]) ∣ (f p).coeff 1 1 := by simpa using a1
  have hB : (p : ℤ_[p]) ∣ (f p).coeff 0 1 := by
    have := (dvd_sub (dvd_sub a2 hA) hC)
    convert this using 1; ring
  have hnu : ∀ z : ℤ_[p], (p : ℤ_[p]) ∣ z → ¬ IsUnit z := fun z hz hu =>
    PadicInt.p_nonunit (isUnit_of_dvd_unit hz hu)
  rcases hprim p with h | h | h
  · exact hnu _ hA h
  · exact hnu _ hB h
  · exact hnu _ hC h

/-- The discriminant of the global form equals $D$ (given local equivalences at all $p$ and at $\infty$). -/
theorem disc_of_local {D : ℤ} (hD : D ≠ 0) (F : BinQF) (f : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℤ_[p] 2)
    (hf : ∀ (p : ℕ) [Fact p.Prime], -(f p).hessian.det = (D : ℤ_[p])) (fInf : QuadForm ℝ 2)
    (hfInf : -fInf.hessian.det = (D : ℝ))
    (hF : ∀ (p : ℕ) [Fact p.Prime], IsometricGL (F.map (Int.castRingHom ℤ_[p])) (f p))
    (hFInf : IsometricGL (F.map (Int.castRingHom ℝ)) fInf) : F.disc = D := by
  have hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ u : ℤ_[p], IsUnit u ∧ (D : ℤ_[p]) = u * (F.disc : ℤ_[p]) := by
    intro p _
    obtain ⟨g, hg⟩ := hF p
    have h1 := disc_transform _ _ g hg
    have h2 := hf p
    rw [Binary.hessian_det_two] at h2
    refine ⟨g.val.det ^ 2, (Matrix.isUnit_iff_isUnit_det _ |>.mp g.isUnit).pow 2, ?_⟩
    simp only [QuadForm.map, Matrix.map_apply, eq_intCast] at h1
    simp only [BinQF.disc, BinQF.a, BinQF.b, BinQF.c]
    push_cast
    linear_combination (-1 : ℤ_[p]) * h2 + h1
  obtain ⟨g, hg⟩ := hFInf
  have h1 := disc_transform _ _ g hg
  have h2 := hfInf
  rw [Binary.hessian_det_two] at h2
  simp only [QuadForm.map, Matrix.map_apply, eq_intCast] at h1
  have hreal : (D : ℝ) = g.val.det ^ 2 * (F.disc : ℝ) := by
    simp only [BinQF.disc, BinQF.a, BinQF.b, BinQF.c]
    push_cast
    linear_combination (-1 : ℝ) * h2 + h1
  have hdet : g.val.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _ |>.mp g.isUnit).ne_zero
  have hF0 : F.disc ≠ 0 := by
    intro h; rw [h] at hreal; apply hD; exact_mod_cast (by simpa using hreal : (D : ℝ) = 0)
  have habs := natAbs_eq_of_unit_mul hF0 hD hloc
  rcases Int.natAbs_eq_natAbs_iff.mp habs with h | h
  · exact h
  · exfalso
    rw [h] at hreal
    push_cast at hreal
    have : (D : ℝ) * (1 + g.val.det ^ 2) = 0 := by linear_combination hreal
    have h3 : (1 + g.val.det ^ 2) ≠ 0 := by positivity
    exact hD (by exact_mod_cast (mul_eq_zero.mp this).resolve_right h3)

/-- **Cassels, Ch. 14, Corollary to Theorem 5.1** (pp. 343–344): *for all $p$ (including $\infty$) let $f_p$ be a
primitive integral $p$-adic form of discriminant $D$. Suppose that $\prod_{p \text{ incl. } \infty} c_p(f_p) = 1$, where
$c_p$ is the Hasse–Minkowski invariant. Then there is a global integral form $f$ which is $\mathbb Z_p$-equivalent to
$f_p$ for each $p$.* Here $D \ne 0$, $f_p$ (`f p`) is a primitive form over $\mathbb Z_p$ for each prime $p$ and
$f_\infty$ (`fInf`) a form over $\mathbb R$; the product is finite by `hasseAt_eq_one_of_not_dvd`. The global form is
primitive of discriminant $D$. -/
@[kb "cassels1978" "Ch. 14, Cor. to Thm. 5.1, pp. 343–344"]
theorem exists_int_form_of_local {D : ℤ} (hD : D ≠ 0) (f : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℤ_[p] 2)
    (hprim : ∀ (p : ℕ) [Fact p.Prime], IsPrimitiveZp (f p))
    (hf : ∀ (p : ℕ) [Fact p.Prime], -(f p).hessian.det = (D : ℤ_[p])) (fInf : QuadForm ℝ 2)
    (hfInf : -fInf.hessian.det = (D : ℝ))
    (hprod : (∏ᶠ p : Nat.Primes, hasseAt (fun q _ => (f q).map PadicInt.Coe.ringHom) p) * hasseC fInf = 1) :
    ∃ F : BinQF, F.IsPrimitive ∧ F.disc = D ∧
      (∀ (p : ℕ) [Fact p.Prime], IsometricGL (F.map (Int.castRingHom ℤ_[p])) (f p)) ∧
      IsometricGL (F.map (Int.castRingHom ℝ)) fInf := by
  have hD' : ((D : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hD
  have hfin : {p : Nat.Primes | hasseAt (fun q _ => (f q).map PadicInt.Coe.ringHom) p ≠ 1}.Finite := by
    have hsub : {p : Nat.Primes | hasseAt (fun q _ => (f q).map PadicInt.Coe.ringHom) p ≠ 1} ⊆
        {p : Nat.Primes | (p : ℕ) ∈ (2 * D).natAbs.divisors} := by
      intro p hp
      by_contra hn
      apply hp
      apply hasseAt_eq_one_of_not_dvd f hprim hf
      intro hdvd
      apply hn
      have h2D : 2 * D ≠ 0 := mul_ne_zero two_ne_zero hD
      exact Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp hdvd, Int.natAbs_ne_zero.mpr h2D⟩
    exact (Set.Finite.preimage (Subtype.val_injective.injOn) (Finset.finite_toSet _)).subset hsub
  have hg : ∀ (p : ℕ) [Fact p.Prime],
      -((f p).map PadicInt.Coe.ringHom).hessian.det
        = (((D : ℤ) : ℚ) : ℚ_[p]) := by
    intro p _
    rw [Rat.cast_intCast]
    exact neg_det_map (hf p)
  have hgInf : -fInf.hessian.det = (((D : ℤ) : ℚ) : ℝ) := by
    rw [Rat.cast_intCast]; exact hfInf
  obtain ⟨G, -, hG, hGInf⟩ := exists_rat_form_of_local ((D : ℤ) : ℚ) hD'
    (fun q _ => (f q).map PadicInt.Coe.ringHom) hg fInf hgInf hfin hprod
  have hfp : ∀ (p : ℕ) [Fact p.Prime], (f p).hessian.det = ((-D : ℤ) : ℤ_[p]) := by
    intro p _
    rw [Int.cast_neg, ← hf p]; ring
  have hfinf : fInf.hessian.det = ((-D : ℤ) : ℝ) := by
    rw [Int.cast_neg, ← hfInf]; ring
  obtain ⟨F, hF1, hF2, -⟩ := Siegel.exists_form_of_local_forms (neg_ne_zero.mpr hD) f hfp fInf hfinf G
    hG hGInf
  exact ⟨F, isPrimitive_of_local F f hprim hF1, disc_of_local hD F f hf fInf hfInf hF1 hF2, hF1, hF2⟩

end QuadFormsKB.Composition
