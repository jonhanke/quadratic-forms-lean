/-
# The singular series of degree $r$ as a limit of truncations
**Layer:** global over a totally real number field $F$.

**Setting.** $\mathrm{Sym}_r(F)/\mathrm{Sym}_r(\mathcal O_F)$ in upper coordinates (`(SymIdx r → F) ⧸ symO F r`); the terms
$s(q) = f_f(w\,n(\tilde q), s_0)\,e_T(\sigma(\tilde q))$ of the singular series `singR` (`ssTermR`); for $c \in \mathcal O_F\setminus 0$, the classes with
$c\tilde q$ integral (`DenDvdR c`), represented by $u_p = \tilde a_p/c$, $a \in (\mathcal O_F/c)^{\{i\le i'\}}$ (`uOf`); $c_X = X!$ (`cX`, as in the degree-one case).

**Results.**
* `ssTermR_mk`: $s$ does not depend on the representative ($f_f$ and $e_T$ are $\mathrm{Sym}_r(\mathcal O_F)$-periodic for $T$ integral).
* `sum_uOf_eq_tsum`: $\sum_{a\in(\mathcal O_F/c)^{\{i\le i'\}}}f_f(w\,n(u_a))e_T(\sigma(u_a)) = \sum_q[c\tilde q \text{ integral}]\,s(q)$.
* **`tendsto_truncSS`** (the double limit): $\lim_X\lim_E\sum_{a}f_f(w\,n(u_a))e_T(\sigma(u_a))|_{c = (X!)^E} = \mathrm{singR}(T)$, in the form
  `tendsto_tsum_denPowR_inner` ($E \to \infty$) and `tendsto_tsum_denPowR_outer` ($X \to \infty$), by dominated convergence over the
  absolutely convergent singular series (`summable_norm_fFinR_quot`).

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. Math. 36 (1935), §§ 3–5 [unverified]; the degree-one
version is `tendsto_ssTrunc_pow`, `tendsto_tsum_denPow` (`SiegelWeil/SingularSeriesNF2.lean`).
-/
import QuadFormsKB.SiegelWeil.Forms.SingularSeriesRProd
import QuadFormsKB.SiegelWeil.SingularSeriesNF

open Matrix NumberField IsDedekindDomain Filter Topology
open QuadFormsKB.HilbertModular QuadFormsKB.Analysis QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- The representatives $u_p = \tilde a_p/c$ of $c^{-1}\mathrm{Sym}_r(\mathcal O_F)/\mathrm{Sym}_r(\mathcal O_F)$. -/
def uOf (c : 𝓞 F) (a : SymIdx r → 𝓞 F ⧸ Ideal.span {c}) : SymIdx r → F := fun p => ιO (Quotient.out (a p)) / ιO c

/-- The class $q = [\tilde q]$ has denominator dividing $c$: $c\tilde q_p \in \mathcal O_F$ for all $p$. -/
def DenDvdR (c : 𝓞 F) (q : (SymIdx r → F) ⧸ symO F r) : Prop := ∀ p, SingularNF.IsDen c (q.out p)

/-- The term $s(q) = f_f(w\,n(\tilde q), s_0)\,e_T(\sigma(\tilde q))$ of the singular series. -/
def ssTermR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T : QuadForm F r) (q : (SymIdx r → F) ⧸ symO F r) : ℂ :=
  fFinR b hb q.out * eT T (realMat (symOf q.out))

lemma singR_eq_tsum (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T : QuadForm F r) :
    singR b hb T = ∑' q, ssTermR b hb T q := rfl

lemma realMat_add (B B' : Matrix (Fin r) (Fin r) F) : realMat (B + B') = realMat B + realMat B' := by
  funext w; ext i j; simp [realMat]

lemma out_mk_sub_mem (u : SymIdx r → F) :
    (QuotientAddGroup.mk u : (SymIdx r → F) ⧸ symO F r).out - u ∈ symO F r := by
  have h : (QuotientAddGroup.mk (QuotientAddGroup.mk u : (SymIdx r → F) ⧸ symO F r).out :
      (SymIdx r → F) ⧸ symO F r) = QuotientAddGroup.mk u := QuotientAddGroup.out_eq' _
  rw [QuotientAddGroup.eq] at h
  have := (symO F r).neg_mem h
  rw [neg_add, neg_neg] at this
  rwa [sub_eq_add_neg]

/-- $s$ is independent of the representative. -/
lemma ssTermR_mk (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T : QuadForm F r) (hT : IsIntMat T.coeff)
    (u : SymIdx r → F) :
    ssTermR b hb T (QuotientAddGroup.mk u) = fFinR b hb u * eT T (realMat (symOf u)) := by
  unfold ssTermR
  set l := (QuotientAddGroup.mk u : (SymIdx r → F) ⧸ symO F r).out - u
  have hl : l ∈ symO F r := out_mk_sub_mem u
  have he : (QuotientAddGroup.mk u : (SymIdx r → F) ⧸ symO F r).out = u + l := by simp [l]
  rw [he, fFinR_add_symO b hb u hl, symOf_add, realMat_add, eT_add,
    eT_realMat_int T hT (symOf_transpose l) (isIntMat_symOf hl), mul_one]

lemma norm_eT_realMat (T : QuadForm F r) (B : Matrix (Fin r) (Fin r) F) : ‖eT T (realMat B)‖ = 1 := by
  rw [norm_eT]; simp [realMat]

/-- The singular series converges absolutely ($m > 4r^2$). -/
lemma summable_norm_ssTermR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (algebraMap (𝓞 F) F (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    (T : QuadForm F r) : Summable fun q => ‖ssTermR b hb T q‖ := by
  refine (summable_norm_fFinR_quot b hb hbpos hr hm).congr fun q => ?_
  rw [ssTermR, norm_mul, norm_eT_realMat, mul_one]

/-! ### The truncation at a modulus $c$ -/

lemma isDen_uOf (c : 𝓞 F) (hc : c ≠ 0) (a : SymIdx r → 𝓞 F ⧸ Ideal.span {c}) (p : SymIdx r) :
    SingularNF.IsDen c (uOf c a p) := by
  refine ⟨Quotient.out (a p), ?_⟩
  have : ιO c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hc
  simp only [uOf]; field_simp

lemma isDen_add_symO {c : 𝓞 F} {u l : SymIdx r → F} (hl : l ∈ symO F r) (p : SymIdx r)
    (h : SingularNF.IsDen c (u p)) : SingularNF.IsDen c ((u + l) p) := by
  obtain ⟨o, ho⟩ := mem_symO.mp hl p
  obtain ⟨a, ha⟩ := h
  exact ⟨a + c * o, by simp only [Pi.add_apply, map_add, map_mul, ha, ho]; ring⟩

lemma denDvdR_mk_iff (c : 𝓞 F) (u : SymIdx r → F) :
    DenDvdR c (QuotientAddGroup.mk u : (SymIdx r → F) ⧸ symO F r) ↔ ∀ p, SingularNF.IsDen c (u p) := by
  have hl := out_mk_sub_mem u
  have hl' : -((QuotientAddGroup.mk u : (SymIdx r → F) ⧸ symO F r).out - u) ∈ symO F r := (symO F r).neg_mem hl
  constructor
  · intro h p
    have := isDen_add_symO hl' p (h p)
    simpa using this
  · intro h p
    have := isDen_add_symO hl p (h p)
    simpa using this

lemma mk_uOf_injective (c : 𝓞 F) (hc : c ≠ 0) :
    Function.Injective fun a : SymIdx r → 𝓞 F ⧸ Ideal.span {c} =>
      (QuotientAddGroup.mk (uOf c a) : (SymIdx r → F) ⧸ symO F r) := by
  intro a a' h
  simp only at h
  rw [QuotientAddGroup.eq] at h
  funext p
  obtain ⟨o, ho⟩ := mem_symO.mp h p
  have hc' : ιO c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hc
  simp only [Pi.add_apply, Pi.neg_apply, uOf] at ho
  rw [← Ideal.Quotient.mk_out (a p), ← Ideal.Quotient.mk_out (a' p), Ideal.Quotient.eq,
    Ideal.mem_span_singleton']
  refine ⟨-o, ?_⟩
  apply IsFractionRing.injective (𝓞 F) F
  rw [map_mul, map_neg, ho, map_sub]
  field_simp
  ring

lemma range_mk_uOf (c : 𝓞 F) (hc : c ≠ 0) :
    Set.range (fun a : SymIdx r → 𝓞 F ⧸ Ideal.span {c} =>
      (QuotientAddGroup.mk (uOf c a) : (SymIdx r → F) ⧸ symO F r)) = {q | DenDvdR c q} := by
  have hc' : ιO c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hc
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    exact (denDvdR_mk_iff c _).mpr (isDen_uOf c hc a)
  · intro hq
    choose o ho using hq
    refine ⟨fun p => Ideal.Quotient.mk _ (o p), ?_⟩
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq]
    refine mem_symO.mpr fun p => ?_
    have hmem : Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) (o p)) - o p ∈ Ideal.span {c} := by
      rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨-t, ?_⟩
    simp only [Pi.add_apply, Pi.neg_apply, uOf]
    have e1 : ιO (Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) (o p))) = ιO (t * c) + ιO (o p) := by
      rw [ht]; simp
    rw [e1, ho p, map_neg, map_mul]
    field_simp
    ring

open Classical in
/-- **The truncated singular series**: $\sum_{a\in(\mathcal O_F/c)^{\{i\le i'\}}}f_f(w\,n(u_a))e_T(\sigma(u_a)) = \sum_q[c\tilde q\text{ integral}]\,s(q)$. -/
theorem sum_uOf_eq_tsum (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T : QuadForm F r) (hT : IsIntMat T.coeff)
    (c : 𝓞 F) (hc : c ≠ 0) [Fintype (𝓞 F ⧸ Ideal.span {c})] :
    ∑ a : SymIdx r → 𝓞 F ⧸ Ideal.span {c}, fFinR b hb (uOf c a) * eT T (realMat (symOf (uOf c a))) =
      ∑' q, if DenDvdR c q then ssTermR b hb T q else 0 := by
  set j : (SymIdx r → 𝓞 F ⧸ Ideal.span {c}) → (SymIdx r → F) ⧸ symO F r :=
    fun a => QuotientAddGroup.mk (uOf c a)
  have hj := mk_uOf_injective (r := r) c hc
  have e1 : ∀ a, fFinR b hb (uOf c a) * eT T (realMat (symOf (uOf c a))) = ssTermR b hb T (j a) :=
    fun a => (ssTermR_mk b hb T hT _).symm
  simp_rw [e1]
  rw [← tsum_fintype (L := SummationFilter.unconditional _), ← tsum_range (ssTermR b hb T) hj, range_mk_uOf c hc, tsum_subtype]
  congr 1

/-! ### The double limit -/

/-- $\tilde q$ has a denominator dividing a power of $X!$. -/
def DenPowR (X : ℕ) (q : (SymIdx r → F) ⧸ symO F r) : Prop := ∃ E : ℕ, DenDvdR (SingularNF.cX F X ^ E) q

lemma denDvdR_mul {c : 𝓞 F} {q : (SymIdx r → F) ⧸ symO F r} (h : DenDvdR c q) (d : 𝓞 F) : DenDvdR (c * d) q :=
  fun p => SingularNF.isDen_mul (h p) d

open Classical in
/-- **Step 1** ($E \to \infty$), dominated convergence. -/
theorem tendsto_tsum_denPowR_inner {f : (SymIdx r → F) ⧸ symO F r → ℂ} (hsum : Summable fun q => ‖f q‖) (X : ℕ) :
    Tendsto (fun E : ℕ => ∑' q, if DenDvdR (SingularNF.cX F X ^ E) q then f q else 0) atTop
      (𝓝 (∑' q, if DenPowR X q then f q else 0)) := by
  refine tendsto_tsum_of_dominated_convergence hsum (fun q => ?_) (Eventually.of_forall fun E q => ?_)
  · by_cases hq : DenPowR X q
    · obtain ⟨E₀, hE₀⟩ := hq
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop E₀] with E hE
      have hD : DenDvdR (SingularNF.cX F X ^ E) q := by
        have := denDvdR_mul hE₀ (SingularNF.cX F X ^ (E - E₀))
        rwa [← pow_add, Nat.add_sub_cancel' hE] at this
      rw [if_pos ⟨E₀, hE₀⟩, if_pos hD]
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun E => ?_)
      have hD : ¬ DenDvdR (SingularNF.cX F X ^ E) q := fun h => hq ⟨E, h⟩
      simp only [if_neg hq, if_neg hD]
  · split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _

/-- Every class has a denominator dividing $X!$ for all large $X$. -/
lemma exists_denDvdR_cX (q : (SymIdx r → F) ⧸ symO F r) : ∃ M, ∀ X, M ≤ X → DenDvdR (SingularNF.cX F X) q := by
  choose d hd0 hd using fun p => SingularNF.exists_isDen (F := F) (q.out p)
  set c0 : 𝓞 F := ∏ p, d p
  have hc0 : c0 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hd0 p
  have hden : ∀ p, SingularNF.IsDen c0 (q.out p) := by
    intro p
    have := SingularNF.isDen_mul (hd p) (∏ p' ∈ Finset.univ.erase p, d p')
    rwa [Finset.mul_prod_erase _ _ (Finset.mem_univ p)] at this
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {c0}))
  set M := Ideal.absNorm (Ideal.span {c0})
  have hM : 0 < M := Nat.pos_of_ne_zero (by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact SingularNF.span_ne_bot hc0)
  refine ⟨M, fun X hX p => ?_⟩
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hM hX
  have := SingularNF.isDen_mul (SingularNF.isDen_mul (hden p) t) (k : 𝓞 F)
  rwa [show c0 * t * (k : 𝓞 F) = SingularNF.cX F X by rw [SingularNF.cX, hk, Nat.cast_mul, ← ht]; ring] at this

open Classical in
/-- **Step 2** ($X \to \infty$): every denominator divides some $X!$. -/
theorem tendsto_tsum_denPowR_outer {f : (SymIdx r → F) ⧸ symO F r → ℂ} (hsum : Summable fun q => ‖f q‖) :
    Tendsto (fun X : ℕ => ∑' q, if DenPowR X q then f q else 0) atTop (𝓝 (∑' q, f q)) := by
  refine tendsto_tsum_of_dominated_convergence hsum (fun q => ?_) (Eventually.of_forall fun X q => ?_)
  · obtain ⟨M, hM⟩ := exists_denDvdR_cX q
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop M] with X hX
    rw [if_pos ⟨1, by rw [pow_one]; exact hM X hX⟩]
  · split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _

end QuadFormsKB.SiegelWeil.Forms
