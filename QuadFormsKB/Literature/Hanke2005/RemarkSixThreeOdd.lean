/-
# Hanke 2005, remark after Theorem 6.3 ($n$ odd): $t_{\mathfrak p} = 1$ iff the Hasse invariant is that of $\mathbb H^m\perp\langle(-1)^m d\rangle$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**The printed remark** (thesis, p. 21, after Theorem 6.3): "In terms of the invariants $(n_p, d_p, c_p)$ of the local
quadratic space $(V_p,\varphi_p)$, the condition $t_v = 1$ is equivalent to
$c_p = ((-1)^{n/2}, (-1)^{n/2}d_p)_p$ when $n$ is odd."

**What is proved here (all $n = 2m+1$ odd).** Let $K = F_{\mathfrak p}$ be the completion of a number field at a finite place,
$V_{\mathfrak p}\cong\langle a_0,\dots,a_{n-1}\rangle$ with all $a_i\in K^\times$ and $d = \prod_i a_i$. Then
$t_{\mathfrak p} = \dim(\text{anisotropic kernel})\in\{1,3\}$ (`anisoDim`), and
$$ t_{\mathfrak p} = 1 \iff V_{\mathfrak p}\cong\mathbb H^m\perp\langle(-1)^m d\rangle
\iff \varepsilon(\langle a_0,\dots,a_{n-1}\rangle) = \varepsilon(\langle1,-1,\dots,1,-1,(-1)^md\rangle)
= (-1,-1)_K^{\binom m2}\,\bigl(-1,(-1)^m d\bigr)_K^{\,m}, $$
where $\varepsilon(\langle a\rangle) = \prod_{i<j}(a_i,a_j)_K$ is **Serre's Hasse invariant = Cassels' $c$**
(`PadicClass.hasseVec`; Serre IV §2.1, Cassels Ch. 4 §1): `anisoDim_eq_one_iff_hasseVec`, the headline, and `wittIndex_eq_iff_hasseVec` over any field satisfying
the local Hilbert-symbol axioms (`PadicClass.LocalHilbertField`). The value $\binom m2 = m(m-1)/2$ and the
exponent $m$ come from $\mathbb H^m = \langle1,-1\rangle^m$: pairs among the $2m$ hyperbolic entries contribute
$(-1,-1)^{\binom m2}$ (only the pairs of two entries $-1$ are nontrivial), and the last entry $e = (-1)^md$ pairs
with the $m$ entries $-1$ (`hasseVec_hypDiagOdd`). By $m \bmod 4$:
$m\equiv0$: $1$; $m\equiv1$: $(-1,-d)$; $m\equiv2$: $(-1,-1)$; $m\equiv3$: $(-1,d)$ (using $(-1,e)^m=(-1,e)^{m\bmod2}$,
$e=(-1)^md$, and $(-1,-1)^{\binom m2}$ nontrivial exactly for $m\equiv2,3\bmod4$).

*Erratum / update (formalization, 2026-11-02):* the printed exponent $n/2$ is not an integer for odd $n$. The remark is
correct in spirit (the condition $t = 1$ is a condition on $c_p$ given $d_p$), but the right-hand side in Serre/Cassels'
convention is the displayed $(-1,-1)^{\binom m2}(-1,(-1)^md)^m$, $m = (n-1)/2$, which is **not** of the printed shape
$(x, x d_p)$ for a single sign $x = (-1)^k$ (for $m = 2$ it is $(-1,-1)$, independent of $d$, whereas $(x,xd)=(x,-d)$ for
$x = -1$ depends on $d$). With O'Meara's $S = \prod_{i\le j}$ the value is $(-1,-1)^{\binom{m+1}2}(-1,e)^{m+1}$.
Also $t_{\mathfrak p}\in\{1,3\}$ for odd $n$ (`anisoDim_parity`, `anisoDim_le_four`), so "$t = 1$" is the complement of
"$t = 3$".
-/
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2005.LocalTypes
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF

open NumberField IsDedekindDomain QuadraticMap QuadraticForm

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

namespace OddAniso

open PadicClass

section Generic

variable {K : Type*} [Field K]

/-- **The diagonal form $\langle1,-1,\dots,1,-1,e\rangle$** with $m$ pairs $1,-1$ followed by $e$, as a vector of $2m+1$
entries (0-based: entries $0,\dots,2m-1$ alternate $1,-1$; entry $2m$ is $e$). It is $\mathbb H^m\perp\langle e\rangle$
(`wss_hypDiagOdd_equiv`). -/
def hypDiagOdd (e : K) : (m : ℕ) → Fin (2 * m + 1) → K
  | 0 => fun _ => e
  | m + 1 => (Fin.cons 1 (Fin.cons (-1) (hypDiagOdd e m)) : Fin (2 * m + 1 + 1 + 1) → K)

theorem hypDiagOdd_succ (e : K) (m : ℕ) :
    hypDiagOdd e (m + 1) = (Fin.cons 1 (Fin.cons (-1) (hypDiagOdd e m)) : Fin (2 * m + 1 + 1 + 1) → K) := rfl

theorem hypDiagOdd_ne_zero (e : K) (he : e ≠ 0) : ∀ (m : ℕ) (i : Fin (2 * m + 1)), hypDiagOdd e m i ≠ 0
  | 0, i => he
  | m + 1, i => by
    rw [hypDiagOdd_succ]
    refine Fin.cases one_ne_zero (fun j => ?_) i
    simp only [Fin.cons_succ]
    refine Fin.cases (neg_ne_zero.2 one_ne_zero) (fun k => ?_) j
    simp only [Fin.cons_succ]
    exact hypDiagOdd_ne_zero e he m k

theorem prod_cons_cons {M : Type*} [CommMonoid M] (f : K → M) {k : ℕ} (w : Fin k → K) :
    ∏ i, f ((Fin.cons 1 (Fin.cons (-1) w) : Fin (k + 1 + 1) → K) i) = f 1 * (f (-1) * ∏ i, f (w i)) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp

theorem prod_hypDiagOdd (e : K) : ∀ m : ℕ, ∏ i, hypDiagOdd e m i = (-1) ^ m * e
  | 0 => by simp [hypDiagOdd]
  | m + 1 => by
    have h : ∏ i, hypDiagOdd e (m + 1) i = 1 * ((-1) * ∏ i, hypDiagOdd e m i) :=
      prod_cons_cons (fun x : K => x) (hypDiagOdd e m)
    rw [h, prod_hypDiagOdd e m]
    ring

/-- The two-step cons: $\langle1,-1,w\rangle \cong \mathbb H\perp\langle w\rangle$ over a field with $2\ne0$. -/
def wssHypEquiv (h2 : (2 : K) ≠ 0) {k : ℕ} (w : Fin k → K) :
    (weightedSumSquares K (Fin.cons 1 (Fin.cons (-1) w) : Fin (k + 1 + 1) → K)).IsometryEquiv
      ((hyperbolicPlane K).prod (weightedSumSquares K w)) where
  toFun x := ((x 0 + x 1, x 0 - x 1), fun j => x j.succ.succ)
  invFun p := Fin.cons ((p.1.1 + p.1.2) / 2) (Fin.cons ((p.1.1 - p.1.2) / 2) p.2)
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' c x := by
    ext <;> simp <;> ring
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp; field_simp; ring
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp; field_simp; ring
      · simp
  right_inv p := by
    ext <;> simp <;> field_simp <;> ring
  map_app' x := by
    simp [weightedSumSquares_apply, Fin.sum_univ_succ]
    ring

theorem wss_hypDiagOdd_equiv (h2 : (2 : K) ≠ 0) (e : K) :
    ∀ m : ℕ, (weightedSumSquares K (hypDiagOdd e m)).Equivalent
      ((hyperbolicSpace K m).prod (weightedSumSquares K (fun _ : Fin 1 => e)))
  | 0 => ⟨(Witt.hyperbolicSpaceZeroProd _).symm⟩
  | m + 1 => by
    rw [hypDiagOdd_succ]
    exact ⟨(wssHypEquiv h2 _).trans (((QuadraticMap.IsometryEquiv.refl _).prod
      (wss_hypDiagOdd_equiv h2 e m).some).trans ((Witt.prodAssoc _ _ _).symm.trans
        ((Witt.hyperbolicSpaceSucc m).prod (QuadraticMap.IsometryEquiv.refl _))))⟩

/-- The Witt index of $\langle1,-1,\dots,1,-1,e\rangle$ ($e\ne0$, $m$ pairs) is $m$. -/
theorem wittIndex_wss_hypDiagOdd (h2 : (2 : K) ≠ 0) {e : K} (he : e ≠ 0) (m : ℕ) :
    wittIndex (weightedSumSquares K (hypDiagOdd e m)) = m := by
  have hrad := SelfDualN.radical_wss h2 (hypDiagOdd e m) (hypDiagOdd_ne_zero e he m)
  have han : (weightedSumSquares K (fun _ : Fin 1 => e)).Anisotropic := by
    intro x hx
    rw [weightedSumSquares_apply] at hx
    simp only [Finset.univ_unique, Finset.sum_singleton, smul_eq_mul] at hx
    funext i
    have : x default * x default = 0 := (mul_eq_zero.1 hx).resolve_left he
    have h0 : x default = 0 := mul_self_eq_zero.1 this
    simpa [Subsingleton.elim i default] using h0
  exact (eq_wittIndex _ hrad han (wss_hypDiagOdd_equiv h2 e m)).symm

end Generic

section Hasse

variable {K : Type*} [Field K] [CharZero K] {k : ℕ}

theorem hasseVec_cons_cons (w : Fin k → K) :
    hasseVec (Fin.cons 1 (Fin.cons (-1) w) : Fin (k + 1 + 1) → K) =
      (∏ j, hilbertSymbol K (-1) (w j)) * hasseVec w := by
  rw [hasseVec_cons_prod, hasseVec_cons_prod, Fin.prod_univ_succ]
  simp [hs_one_left]

theorem prod_hilbert_hypDiagOdd (e : K) : ∀ m : ℕ,
    ∏ j, hilbertSymbol K (-1) (hypDiagOdd e m j) =
      hilbertSymbol K (-1) (-1) ^ m * hilbertSymbol K (-1) e
  | 0 => by simp [hypDiagOdd]
  | m + 1 => by
    have h : ∏ j, hilbertSymbol K (-1) (hypDiagOdd e (m + 1) j) =
        hilbertSymbol K (-1) 1 * (hilbertSymbol K (-1) (-1) * ∏ j, hilbertSymbol K (-1) (hypDiagOdd e m j)) :=
      prod_cons_cons (fun x : K => hilbertSymbol K (-1) x) (hypDiagOdd e m)
    rw [h, prod_hilbert_hypDiagOdd e m, hilbertSymbol_one_right]
    ring

/-- **The Hasse invariant of $\langle1,-1,\dots,1,-1,e\rangle$** ($m$ pairs): Serre's
$\varepsilon = (-1,-1)^{\binom m2}(-1,e)^m$. -/
theorem hasseVec_hypDiagOdd (e : K) : ∀ m : ℕ,
    hasseVec (hypDiagOdd e m) = hilbertSymbol K (-1) (-1) ^ (m.choose 2) * hilbertSymbol K (-1) e ^ m
  | 0 => by simp [hasseVec, hypDiagOdd]
  | m + 1 => by
    rw [hypDiagOdd_succ, hasseVec_cons_cons, prod_hilbert_hypDiagOdd, hasseVec_hypDiagOdd e m,
      Nat.choose_succ_succ, Nat.choose_one_right]
    ring

end Hasse

section Classification

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem toQuadraticFormIn_diag_self (a : Fin n → K) :
    (QuadForm.diag a).toQuadraticFormIn K = weightedSumSquares K a := by
  ext x
  rw [QuadForm.toQuadraticFormIn_apply, SelfDualN.evalIn_diag, weightedSumSquares_apply]
  simp [smul_eq_mul, _root_.sq]

theorem det_hessian_diag (a : Fin n → K) : (QuadForm.diag a).hessian.det = 2 ^ n * ∏ i, a i := by
  rw [SelfDualN.hessian_diag', Matrix.det_diagonal, Finset.prod_mul_distrib]
  simp

/-- `exists_witt_diag_aux` with the Witt index and kernel dimension named: if $n = 2w + t$ and the Witt index is $w$. -/
theorem exists_witt_diag_of_index (h2 : (2 : K) ≠ 0) {n : ℕ} (Q : QuadForm K n) (hQ : Q.Nondegenerate) {w t : ℕ}
    (hw : wittIndex Q.toQuadraticForm = w) (ht : n = 2 * w + t) :
    ∃ a' : Fin t → K, (∀ x : Fin t → K, ∑ i, a' i * x i ^ 2 = 0 → x = 0) ∧
      (∃ c : K, c ≠ 0 ∧ Q.hessian.det = c ^ 2 * (-1) ^ w * 2 ^ t * ∏ i, a' i) ∧
      Q.toQuadraticForm.Equivalent ((hyperbolicSpace K w).prod (weightedSumSquares K a')) := by
  obtain ⟨-, a', h1, h2', h3⟩ := exists_witt_diag_aux h2 Q hQ
  have hwt : t = n - 2 * wittIndex Q.toQuadraticForm := by omega
  subst hwt
  subst hw
  exact ⟨a', h1, h2', h3⟩

/-- **Over a field with the local Hilbert-symbol axioms, for $n = 2m+1$: Witt index $m$ (anisotropic kernel of dimension
$1$) iff Serre's Hasse invariant is that of $\mathbb H^m\perp\langle(-1)^md\rangle$** ($d = \prod a_i$). -/
theorem wittIndex_eq_iff_hasseVec (hK : LocalHilbertField K) (m : ℕ) (a : Fin (2 * m + 1) → K)
    (ha : ∀ i, a i ≠ 0) :
    wittIndex (weightedSumSquares K a) = m ↔
      hasseVec a = hilbertSymbol K (-1) (-1) ^ (m.choose 2) *
        hilbertSymbol K (-1) ((-1) ^ m * ∏ i, a i) ^ m := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  set P : K := ∏ i, a i with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ha i
  set e : K := (-1) ^ m * P with he
  have he0 : e ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hP0
  have hsq : ((-1 : K) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  have hb := hypDiagOdd_ne_zero e he0 m
  have hprod : ∏ i, hypDiagOdd e m i = P := by
    rw [prod_hypDiagOdd, he, ← mul_assoc, hsq, one_mul]
  have hH := hasseVec_hypDiagOdd e m
  rw [← hH]
  have hiff := isometric_iff_invariants hK ha hb
  constructor
  · intro hw
    have hnd := SelfDualN.nondeg_diag h2 a ha
    have hw0 : wittIndex (QuadForm.diag a).toQuadraticForm = m := by
      rw [SelfDualN.toQF_diag]; exact hw
    obtain ⟨a', hanis, ⟨c, hc, hdet⟩, hE⟩ :=
      exists_witt_diag_of_index h2 (QuadForm.diag a) hnd hw0 (t := 1) (by omega)
    rw [det_hessian_diag] at hdet
    rw [SelfDualN.toQF_diag] at hE
    rw [Fin.prod_univ_one] at hdet
    have hc2 : c ^ 2 * a' 0 = (2 ^ m) ^ 2 * e := by
      have h4 : (2 : K) * (c ^ 2 * (-1) ^ m * a' 0 - 2 ^ (2 * m) * P) = 0 := by
        linear_combination (-1 : K) * hdet
      have h5 := (mul_eq_zero.1 h4).resolve_left h2
      rw [he]
      linear_combination (-1 : K) ^ m * h5 - c ^ 2 * a' 0 * hsq
    have hd0 : (2 : K) ^ m / c ≠ 0 := div_ne_zero (pow_ne_zero _ h2) hc
    have ha' : a' 0 = (2 ^ m / c) ^ 2 * e := by
      rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hc)]
      linear_combination hc2
    have e1 : (weightedSumSquares K a).Equivalent (weightedSumSquares K (hypDiagOdd e m)) :=
      ⟨hE.some.trans (((QuadraticMap.IsometryEquiv.refl _).prod (SelfDualN.scaleIso e _ hd0 a' ha')).trans
        (wss_hypDiagOdd_equiv h2 e m).some.symm)⟩
    have hiso : (QuadForm.diag a).IsometricIn K (QuadForm.diag (hypDiagOdd e m)) := by
      rw [QuadForm.isometricIn_iff_equivalent, toQuadraticFormIn_diag_self, toQuadraticFormIn_diag_self]
      exact ⟨e1.some.symm⟩
    exact (hiff.1 hiso).2
  · intro hh
    have hiso := hiff.2 ⟨⟨1, one_ne_zero, by rw [hprod]; ring⟩, hh⟩
    rw [QuadForm.isometricIn_iff_equivalent, toQuadraticFormIn_diag_self, toQuadraticFormIn_diag_self] at hiso
    have hrad := SelfDualN.radical_wss h2 _ hb
    exact (wittIndex_eq_of_equivalent hiso hrad).symm.trans (wittIndex_wss_hypDiagOdd h2 he0 m)

end Classification

end OddAniso

/-! ### The headline: $t_{\mathfrak p}$ for odd $n$ -/

section Headline

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

open PadicClass in
/-- **Remark after Theorem 6.3, $n$ odd** (Hanke thesis, p. 21): for $n = 2m+1$, $Q_0$ nondegenerate over $\mathcal O_F$ and
$\langle a_0,\dots,a_{n-1}\rangle$ ($a_i\in F_{\mathfrak p}^\times$) any diagonalization of $\varphi_{\mathfrak p} = Q_0\otimes F_{\mathfrak p}$,
$$ t_{\mathfrak p} = 1 \iff c_{\mathfrak p} = \bigl(-1,-1\bigr)_{\mathfrak p}^{\binom m2}\bigl(-1,(-1)^md_{\mathfrak p}\bigr)_{\mathfrak p}^{m},
\qquad d_{\mathfrak p} = \textstyle\prod_i a_i,\ c_{\mathfrak p} = \prod_{i<j}(a_i,a_j)_{\mathfrak p}, $$
the right-hand side being the Hasse invariant $c$ of $\mathbb H^m\perp\langle(-1)^md_{\mathfrak p}\rangle$.
*Erratum:* the printed $((-1)^{n/2},(-1)^{n/2}d_p)_p$ has a non-integer exponent for odd $n$ and is not of this form
(see the module docstring). Indices are 0-based. Unconditional (proved from the Hilbert-symbol axioms at $F_{\mathfrak p}$,
`HasseIsoNF.localHilbertField_adicCompletion`, themselves proved, dyadic places included). -/
@[kb "hanke2005crelle" "Remark after Theorem 6.3, p. 21 (n odd)"]
theorem anisoDim_eq_one_iff_hasseVec (m : ℕ) (Q₀ : QuadForm (𝓞 F) (2 * m + 1)) (hQ : Q₀.Nondegenerate)
    (a : Fin (2 * m + 1) → Fv) (ha : ∀ i, a i ≠ 0)
    (hQa : (Qf v Q₀).toQuadraticForm.Equivalent (weightedSumSquares Fv a)) :
    anisoDim v Q₀ = 1 ↔
      hasseVec a = hilbertSymbol Fv (-1) (-1) ^ (m.choose 2) *
        hilbertSymbol Fv (-1) ((-1) ^ m * ∏ i, a i) ^ m := by
  have : CharZero Fv := charZero_of_injective_algebraMap (algebraMap F Fv).injective
  have hK := HasseIsoNF.localHilbertField_adicCompletion (F := F) v
  have hle := two_mul_wittIndex_le v Q₀ hQ
  rw [QV_eq_Qf] at hle
  have hQf := nondegenerate_Qf v Q₀ hQ
  have hrad : (Qf v Q₀).toQuadraticForm.radical = ⊥ :=
    radical_eq_bot_of_nondegenerate _ (polar_nondeg_toQuadraticForm _ hQf)
  have hw := wittIndex_eq_of_equivalent hQa hrad
  rw [← OddAniso.wittIndex_eq_iff_hasseVec hK m a ha, ← hw, anisoDim_eq]
  omega

end Headline

end QuadFormsKB.Hanke2005
