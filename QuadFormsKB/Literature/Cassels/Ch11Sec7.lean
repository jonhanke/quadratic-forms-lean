/-
# Cassels, Chapter 11, Theorem 7.1: primitive representation by the spinor genus

**Layer:** lattices `L : Lat F n` on $V = (F^n, Q)$ over a number field $F$, $Q$ regular, $n \ge 4$; localizations
`loc v L` at the finite primes; the proper spinor genus `SameProperSpinorGenus` (O'Meara 102A), which is Cassels'
spinor genus. Cassels' statement is over $\mathbb Q$ (the case $F = \mathbb Q$, `exists_sameProperSpinorGenus_primitive_rat`).

**Defines** primitive vectors: $y \in M$ is *primitive* in a lattice $M$ over $\mathfrak o_\mathfrak p$ if $ty \in M$
($t \in F_\mathfrak p$) forces $t \in \mathfrak o_\mathfrak p$ (`LocPrimitive`), and $x \in L$ is primitive in a lattice $L$
over $\mathcal O_F$ if $tx \in L$ ($t \in F$) forces $t \in \mathcal O_F$ (`LatPrimitive`). For $L = \mathbb Z^n$ these
are Cassels' primitive representations: $x = (b_0, \dots, b_{n-1})$ with $\gcd(b_0, \dots, b_{n-1}) = 1$, and over
$\mathbb Z_p$ some $b_i$ a unit.

**Proves** Cassels' Theorem 7.1 (Ch. 11, p. 227) in lattice form (`exists_sameProperSpinorGenus_primitive`): *if
$a \ne 0$ is represented by $V$ over every real (and complex) completion and primitively by $L_\mathfrak p$ at every
finite prime, then $a$ is primitively represented by some lattice in the (proper) spinor genus of $L$.*

*Proof (not Cassels').* Cassels combines Chapter 9, Theorem 1.3, Lemma 4.3, Lemma 4.2 of Chapter 9 and Theorem 6.2,
Corollary. Here the argument is adelic: by the Hasse principle $a = Q(x)$ with $x \in V$; $x$ is primitive in
$L_\mathfrak p$ for almost all $\mathfrak p$ (`eventually_locPrimitive`); at the remaining primes Witt's theorem gives
$\gamma_\mathfrak p \in O^+(V_\mathfrak p)$ with $\gamma_\mathfrak p x = y_\mathfrak p$, a primitive representation of $a$
by $L_\mathfrak p$ (`exists_soSub_mulVec_eq_local`), and, since $x^\perp$ has dimension $n - 1 \ge 3$, a rotation
$\sigma_\mathfrak p$ of $V_\mathfrak p$ fixing $x$ with $\theta(\sigma_\mathfrak p) = \theta(\gamma_\mathfrak p)$
(`exists_soSub_fix_spinorNorm`). The adele $\delta = (\sigma_\mathfrak p\gamma_\mathfrak p^{-1})$ lies in the spinor
kernel $J'_V$, so $M = \delta L$ is in the proper spinor genus of $L$, and $x = \delta_\mathfrak p y_\mathfrak p$ is
primitive in $M_\mathfrak p$ for every $\mathfrak p$, hence in $M$ (`latPrimitive_of_forall_loc`). This is the
argument of O'Meara 102:7 for representations of a vector rather than a sublattice.
-/
import QuadFormsKB.Literature.OMeara.Sec102Rep
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Literature.Cassels.Ch11Sec3
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain

open NumberField IsDedekindDomain Matrix Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Primitive vectors -/

section Primitive

variable (v : HeightOneSpectrum (𝓞 F))

/-- **A primitive vector of a local lattice** (Cassels, Ch. 11, p. 227, over $\mathbb Z_p$): $y \in M$, and
$ty \in M$ with $t \in F_\mathfrak p$ only for $t \in \mathfrak o_\mathfrak p$. For $M = \mathfrak o_\mathfrak p^n$: some
coordinate of $y$ is a unit. -/
@[kb "cassels1978" "Ch. 11, Thm. 7.1, p. 227 (primitive representation over ℤ_p)"]
def LocPrimitive (M : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F))
    (y : Fin n → v.adicCompletion F) : Prop :=
  y ∈ M ∧ ∀ t : v.adicCompletion F, t • y ∈ M → Valued.v t ≤ 1

/-- **A primitive vector of a lattice** (Cassels, Ch. 11, p. 227, over $\mathbb Z$): $x \in L$, and $tx \in L$ with
$t \in F$ only for $t \in \mathcal O_F$. For $L = \mathbb Z^n$: the coordinates of $x$ are coprime. -/
@[kb "cassels1978" "Ch. 11, Thm. 7.1, p. 227 (primitive representation over ℤ)"]
def LatPrimitive (L : Submodule (𝓞 F) (Fin n → F)) (x : Fin n → F) : Prop :=
  x ∈ L ∧ ∀ t : F, t • x ∈ L → t ∈ (algebraMap (𝓞 F) F).range

variable {v}

/-- **Primitivity is local:** if $x$ is primitive in $L_\mathfrak p$ for every $\mathfrak p$, it is primitive in $L$. -/
theorem latPrimitive_of_forall_loc {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) {x : Fin n → F}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), LocPrimitive v (loc v L) (locVec v x)) : LatPrimitive L x := by
  refine ⟨(mem_iff_forall_loc hL x).2 fun v => (h v).1, fun t ht => ?_⟩
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one F t
  intro v
  have e : locVec v (t • x) = algebraMap F (v.adicCompletion F) t • locVec v x := by
    rw [LinearMap.map_smul]; funext i; simp [Algebra.smul_def]
  have := (h v).2 (algebraMap F _ t) (by rw [← e]; exact locVec_mem_loc v ht)
  rwa [valued_algebraMap] at this

/-- **Primitivity is preserved by a linear automorphism:** if $y$ is primitive in $M$, then $gy$ is primitive in
$gM$. -/
theorem LocPrimitive.locAct {M : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)}
    {y : Fin n → v.adicCompletion F} (h : LocPrimitive v M y) (g : GL (Fin n) (v.adicCompletion F)) :
    LocPrimitive v (Lattices.locAct v g M) (g.val *ᵥ y) := by
  refine ⟨⟨y, h.1, rfl⟩, fun t ht => ?_⟩
  obtain ⟨y', hy', e⟩ := mem_locAct.mp ht
  have hy'' : y' = t • y := by
    have := congrArg (fun z => (g⁻¹).val *ᵥ z) e
    simp only [mulVec_mulVec, mulVec_smul] at this
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, one_mulVec] at this
  exact h.2 t (hy'' ▸ hy')

/-- **A nonzero vector is primitive in $L_\mathfrak p$ for almost all $\mathfrak p$.** -/
theorem eventually_locPrimitive {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) {x : Fin n → F}
    (hx : x ≠ 0) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, LocPrimitive v (loc v L) (locVec v x) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push Not at h; exact hx (funext h)
  have hint : ∀ j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, v.valuation F (x j) ≤ 1 := fun j => by
    by_cases hj : x j = 0
    · exact Eventually.of_forall fun v => by simp [hj]
    · filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 F) (x j)).compl_mem_cofinite] with v hv
      simp only [Set.mem_compl_iff, HeightOneSpectrum.Support, Set.mem_ofPred_eq, not_lt] at hv
      exact hv
  have hunit : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, v.valuation F (x i) = 1 := by
    filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 F) (x i)).compl_mem_cofinite,
      (HeightOneSpectrum.Support.finite (𝓞 F) (x i)⁻¹).compl_mem_cofinite] with v hv hv'
    simp only [Set.mem_compl_iff, HeightOneSpectrum.Support, Set.mem_ofPred_eq, not_lt] at hv hv'
    rw [map_inv₀] at hv'
    refine le_antisymm hv ?_
    have h0 : v.valuation F (x i) ≠ 0 := by simpa using hi
    rwa [inv_le_one₀ (zero_lt_iff.mpr h0)] at hv'
  filter_upwards [loc_eventually_std hL, eventually_all.mpr hint, hunit] with v hstd hle h1
  rw [hstd]
  refine ⟨fun j => ?_, fun t ht => ?_⟩
  · rw [locVec_apply, valued_algebraMap]; simpa using hle j
  · have := ht i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, locVec_apply, valued_algebraMap, h1, mul_one] at this
    simpa using this

end Primitive

/-! ### An orthogonal frame through a vector -/

section Frame

variable (Q : QuadForm F n)

/-- **An orthogonal frame through $x$:** for $Q$ regular and $Q(x) \ne 0$ there are an invertible $P$ with first column
$x$ and $b_0, \dots, b_{n-1} \ne 0$ such that $Q(Pz) = \sum_i b_iz_i^2$ over every field $K \supseteq F$. -/
theorem exists_frame (hQ : Q.Nondegenerate) {d : ℕ} (hn : n = d + 1) {x : Fin n → F}
    (hx : Q.evalIn F x ≠ 0) :
    ∃ (P : Matrix (Fin n) (Fin n) F) (b : Fin n → F), IsUnit P.det ∧ (∀ i, b i ≠ 0) ∧
      P *ᵥ Pi.single ⟨0, by omega⟩ 1 = x ∧
      ∀ (K : Type) [Field K] [Algebra F K] (z : Fin n → K),
        Q.evalIn K (P.map (algebraMap F K) *ᵥ z) = (QuadForm.diag b).evalIn K z := by
  classical
  subst hn
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, hwo, hw0⟩ := QuadForm.exists_orthogonal_basis_cons (QuadForm.halfBilin_isSymm Q)
    (x := x) (by rw [QuadForm.halfBilin_self]; exact hx) (Module.finrank_fin_fun F)
  obtain ⟨hne, -⟩ := QuadForm.isometric_diag_of_basis Q hQ w fun i j hij => hwo hij
  set P := (Pi.basisFun F (Fin (d + 1))).toMatrix w with hPdef
  have hmv : ∀ z : Fin (d + 1) → F, P *ᵥ z = ∑ j, z j • w j := fun z => by
    funext i
    simp [P, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, mul_comm]
  have hPF : ∀ z : Fin (d + 1) → F, Q.evalIn F (P *ᵥ z) =
      (QuadForm.diag fun i => Q.evalIn F (w i)).evalIn F z := fun z => by
    rw [← QuadForm.halfBilin_self, hmv, QuadForm.evalIn_diag]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i, ← QuadForm.halfBilin_self]
    · simp; ring
    · intro j _ hj; simp [hwo hj]
    · simp
  refine ⟨P, fun i => Q.evalIn F (w i), ?_, hne, ?_, ?_⟩
  · rw [hPdef, ← Module.Basis.det_apply]; exact Module.Basis.isUnit_det _ _
  · rw [hmv]
    simp [Pi.single_apply, hw0]
  · intro K _ _ z
    -- transfer the polynomial identity from `F` to `K`
    have keyF : ∀ (φ : MvPolynomial (Fin (d + 1)) F →ₐ[F] F) (R : QuadForm F (d + 1))
        (u : Fin (d + 1) → MvPolynomial (Fin (d + 1)) F),
        φ (QuadForm.evalIn _ R u) = QuadForm.evalIn F R (fun i => φ (u i)) := by
      intro φ R u
      simp [QuadForm.evalIn, map_sum, apply_ite, map_mul]
    have keyK : ∀ (φ : MvPolynomial (Fin (d + 1)) F →ₐ[F] K) (R : QuadForm F (d + 1))
        (u : Fin (d + 1) → MvPolynomial (Fin (d + 1)) F),
        φ (QuadForm.evalIn _ R u) = QuadForm.evalIn K R (fun i => φ (u i)) := by
      intro φ R u
      simp [QuadForm.evalIn, map_sum, apply_ite, map_mul]
    have mvF : ∀ (φ : MvPolynomial (Fin (d + 1)) F →ₐ[F] F) (u : Fin (d + 1) → MvPolynomial (Fin (d + 1)) F),
        (fun i => φ ((P.map (algebraMap F _)).mulVec u i)) = P.mulVec (fun i => φ (u i)) := by
      intro φ u
      funext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    have mvK : ∀ (φ : MvPolynomial (Fin (d + 1)) F →ₐ[F] K) (u : Fin (d + 1) → MvPolynomial (Fin (d + 1)) F),
        (fun i => φ ((P.map (algebraMap F _)).mulVec u i)) = (P.map (algebraMap F K)).mulVec (fun i => φ (u i)) := by
      intro φ u
      funext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    have hF : QuadForm.evalIn (MvPolynomial (Fin (d + 1)) F) Q
        ((P.map (algebraMap F (MvPolynomial (Fin (d + 1)) F))).mulVec (fun i => MvPolynomial.X i))
        = QuadForm.evalIn (MvPolynomial (Fin (d + 1)) F) (QuadForm.diag fun i => Q.evalIn F (w i))
          (fun i => MvPolynomial.X i) := by
      apply MvPolynomial.funext
      intro r
      rw [← MvPolynomial.coe_aeval_eq_eval]
      change (MvPolynomial.aeval r) _ = (MvPolynomial.aeval r) _
      rw [keyF, keyF, mvF]
      simp only [MvPolynomial.aeval_X]
      exact hPF r
    have e := congrArg (MvPolynomial.aeval (R := F) (S₁ := K) z) hF
    rw [keyK, keyK, mvK] at e
    simpa only [MvPolynomial.aeval_X] using e

end Frame

/-! ### Local rotations fixing a vector -/

section Local

variable {Q : QuadForm F n}

/-- In a frame $P$ (`exists_frame`), $Pz$ is orthogonal to the first column $Pe_{i_0}$ when $z_{i_0} = 0$. -/
theorem frame_orth {P : Matrix (Fin n) (Fin n) F} {b : Fin n → F} {i0 : Fin n}
    (hP : ∀ (K : Type) [Field K] [Algebra F K] (z : Fin n → K),
      Q.evalIn K (P.map (algebraMap F K) *ᵥ z) = (QuadForm.diag b).evalIn K z)
    (K : Type) [Field K] [Algebra F K] {z : Fin n → K} (hz : z i0 = 0) :
    (P.map (algebraMap F K) *ᵥ z) ⬝ᵥ
      (Q.hessian.map (algebraMap F K) *ᵥ (P.map (algebraMap F K) *ᵥ Pi.single i0 1)) = 0 := by
  rw [← QuadForm.polar_eq_hessian, ← mulVec_add, hP, hP, hP, QuadForm.evalIn_diag, QuadForm.evalIn_diag,
    QuadForm.evalIn_diag, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : i = i0
  · subst h; simp [hz]
  · simp [h]

/-- A symmetry in a vector orthogonal to $y$ fixes $y$. -/
theorem symm_mulVec_of_orth {K : Type} [Field K] [Algebra F K] [CharZero K] {X y : Fin n → K}
    (hX : Q.evalIn K X ≠ 0) (h : X ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ y) = 0) :
    ((symm Q K X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y = y := by
  rw [symm_mulVec Q K hX, h]; simp

/-- The first column of a frame, over $K$. -/
theorem frame_col {P : Matrix (Fin n) (Fin n) F} {i0 : Fin n} {x : Fin n → F} (hPx : P *ᵥ Pi.single i0 1 = x)
    (K : Type) [Field K] [Algebra F K] :
    (fun i => algebraMap F K (x i)) = P.map (algebraMap F K) *ᵥ Pi.single i0 1 := by
  rw [← hPx]; funext i
  rw [RingHom.map_mulVec]
  congr 1; funext j; simp [Pi.single_apply, apply_ite]

variable (Q) (v : HeightOneSpectrum (𝓞 F))

/-- **Rotations fixing $x$ have every spinor norm** (the local step of Cassels' Theorem 7.1; cf. Lemma 3.1): if
$n \ge 4$ and $Q(x) \ne 0$, then for every $a \in F_\mathfrak p^\times$ there is $\sigma \in O^+(V_\mathfrak p)$ with
$\sigma x = x$ and $\theta(\sigma) = aF_\mathfrak p^{\times 2}$ (Lemma 3.1 applied to $x^\perp$, of dimension
$n - 1 \ge 3$). -/
theorem exists_soSub_fix_spinorNorm (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {x : Fin n → F}
    (hx : Q.evalIn F x ≠ 0) (a : (v.adicCompletion F)ˣ) :
    ∃ σ ∈ Tamagawa.soSub Q (v.adicCompletion F),
      ((σ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ locVec v x = locVec v x ∧
        spinorNorm Q (v.adicCompletion F) σ = SqClass.mk a := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  obtain ⟨P, b, -, hb, hPx, hP⟩ := exists_frame Q hQ rfl hx
  set K := v.adicCompletion F
  set b' : Fin d → K := fun i => algebraMap F K (b i.succ) with hb'def
  have hb' : ∀ i, b' i ≠ 0 := fun i => (map_ne_zero _).mpr (hb _)
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  set c : Fin (d + d) → K := Fin.append b' fun i => -(a : K) * b' i with hcdef
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [c, Fin.append_left]; exact hb' j
    · simp only [c, Fin.append_right]; exact mul_ne_zero (neg_ne_zero.mpr ha0) (hb' j)
  have hD : (QuadForm.diag c).IsotropicIn K := by
    refine FieldGen.isotropicIn_diag_of_prefix (F := K) K 5 (by omega) c ?_
    exact LocalRankFive.isotropic_diag_five v (fun i : Fin 5 => c ⟨i, lt_of_lt_of_le i.2 (by omega)⟩)
      (fun i => hc _)
  obtain ⟨X', Y', hY, hXY⟩ := exists_diag_eq_mul_of_isotropic (by omega : 0 < d) b' hb' hD
  have hdiag : ∀ z' : Fin d → K, Q.evalIn K (P.map (algebraMap F K) *ᵥ Fin.cons 0 z') =
      (QuadForm.diag b').evalIn K z' := by
    intro z'
    rw [hP, QuadForm.evalIn_diag, QuadForm.evalIn_diag, Fin.sum_univ_succ]
    simp [b']
  rw [← hdiag] at hY
  rw [← hdiag, ← hdiag] at hXY
  obtain ⟨h1, h2⟩ := symm_mul_symm_spec hQ hY ha0 hXY
  refine ⟨_, h1, ?_, by rw [h2, sqClassOf_of_ne_zero ha0]; exact congrArg SqClass.mk (Units.ext rfl)⟩
  have hloc : locVec v x = P.map (algebraMap F K) *ᵥ Pi.single ⟨0, by omega⟩ 1 := by
    rw [← frame_col hPx K]; rfl
  have hX0 : Q.evalIn K (P.map (algebraMap F K) *ᵥ Fin.cons 0 X') ≠ 0 := by
    rw [hXY]; exact mul_ne_zero ha0 hY
  rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hloc,
    symm_mulVec_of_orth hY (frame_orth (i0 := ⟨0, by omega⟩) hP K (z := Fin.cons 0 Y') (Fin.cons_zero _ _)),
    symm_mulVec_of_orth hX0 (frame_orth (i0 := ⟨0, by omega⟩) hP K (z := Fin.cons 0 X') (Fin.cons_zero _ _))]

/-- **Witt's theorem with a rotation** (for one vector, $n \ge 2$): if $Q(y) = Q(x) \ne 0$ for $y \in V_\mathfrak p$, then
$\gamma x = y$ for some $\gamma \in O^+(V_\mathfrak p)$. -/
theorem exists_soSub_mulVec_eq_local (hQ : Q.Nondegenerate) (hn : 2 ≤ n) {x : Fin n → F}
    (hx : Q.evalIn F x ≠ 0) {y : Fin n → v.adicCompletion F}
    (hy : Q.evalIn (v.adicCompletion F) y = algebraMap F _ (Q.evalIn F x)) :
    ∃ γ ∈ Tamagawa.soSub Q (v.adicCompletion F),
      ((γ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ locVec v x = y := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  obtain ⟨P, b, -, hb, hPx, hP⟩ := exists_frame Q hQ rfl hx
  obtain ⟨γ, hγ, hγx⟩ := exists_orth_mulVec_eq_local Q v (x := locVec v x) (y := y)
    (by rw [evalIn_locVec]; exact hy.symm) (by rw [evalIn_locVec]; exact (map_ne_zero _).mpr hx)
  set K := v.adicCompletion F
  rcases Tamagawa.det_eq_one_or_neg_one Q hQ ⟨γ, hγ⟩ with h1 | h1
  · exact ⟨⟨γ, hγ⟩, h1, hγx⟩
  · set i1 : Fin (d + 1) := ⟨1, by omega⟩
    set W := P.map (algebraMap F K) *ᵥ Pi.single i1 1
    have hW : Q.evalIn K W ≠ 0 := by
      rw [hP, evalIn_diag_single]; simpa using hb i1
    have hloc : locVec v x = P.map (algebraMap F K) *ᵥ Pi.single ⟨0, by omega⟩ 1 := by
      rw [← frame_col hPx K]; rfl
    refine ⟨⟨γ, hγ⟩ * symm Q K W, ?_, ?_⟩
    · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul, symm_det Q K hW]
      change γ.val.det * _ = 1
      rw [show γ.val.det = -1 from h1]; norm_num
    · rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hloc,
        symm_mulVec_of_orth hW (frame_orth (i0 := ⟨0, by omega⟩) hP K (z := Pi.single i1 1) (by simp [i1])), ← hloc]
      exact hγx

end Local

/-! ### Theorem 7.1 -/

section Main

variable (Q : QuadForm F n)

/-- **Moving local representations onto $x$ by the spinor kernel:** if $n \ge 4$, $Q(x) \ne 0$, and $y_\mathfrak p \in
V_\mathfrak p$ has $Q(y_\mathfrak p) = Q(x)$ for every $\mathfrak p$, then for any property `good` of primes holding
for almost all $\mathfrak p$ there is $\delta \in J'_V$ with $\delta_\mathfrak p = 1$ where `good` holds and
$\delta_\mathfrak p y_\mathfrak p = x$ elsewhere: $\delta_\mathfrak p = \sigma_\mathfrak p\gamma_\mathfrak p^{-1}$ with
$\gamma_\mathfrak p x = y_\mathfrak p$ (`exists_soSub_mulVec_eq_local`) and $\sigma_\mathfrak p$ fixing $x$ with
$\theta(\sigma_\mathfrak p) = \theta(\gamma_\mathfrak p)$ (`exists_soSub_fix_spinorNorm`). -/
theorem exists_spinorKernelAf_move (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {x : Fin n → F}
    (hx0 : Q.evalIn F x ≠ 0) (good : HeightOneSpectrum (𝓞 F) → Prop)
    (hgood : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, good v)
    (y : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (hy : ∀ v, Q.evalIn (v.adicCompletion F) (y v) = algebraMap F _ (Q.evalIn F x)) :
    ∃ δ ∈ spinorKernelAf Q, ∀ v, (good v → δ v = 1) ∧
      (¬ good v → (((δ v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ y v = locVec v x) := by
  classical
  choose γ hγs hγx using fun v => exists_soSub_mulVec_eq_local Q v hQ (by omega) hx0 (y := y v) (hy v)
  choose c hc using fun v => SqClass.ind
    (P := fun s : SqClass (v.adicCompletion F) => ∃ c : (v.adicCompletion F)ˣ, SqClass.mk c = s)
    (fun c => ⟨c, rfl⟩) (spinorNorm Q (v.adicCompletion F) (γ v))
  choose σ hσs hσx hσθ using fun v => exists_soSub_fix_spinorNorm Q v hQ hn hx0 (c v)
  obtain ⟨δ, hδ⟩ : ∃ δ : OAf Q, ∀ v, δ v = if good v then 1 else σ v * (γ v)⁻¹ :=
    ⟨⟨fun v => if good v then 1 else σ v * (γ v)⁻¹, by
      filter_upwards [hgood] with v hv
      simp only [hv, ↓reduceIte]
      exact (stdStab Q v).one_mem⟩, fun v => rfl⟩
  refine ⟨δ, ?_, fun v => ⟨fun hv => by rw [hδ v, if_pos hv], fun hv => ?_⟩⟩
  · rw [mem_spinorKernelAf]
    intro v
    rw [hδ v]
    split_ifs
    · exact (spinorKernel Q _).one_mem
    · rw [spinorKernel_eq_ker Q _ hQ, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]
      refine ⟨?_, ?_⟩
      · rw [map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hσθ, hc, mul_inv_cancel]
      · rw [map_mul, map_inv]
        have h1 : detHom Q _ (σ v) = 1 := Units.ext (by rw [detHom_val]; exact hσs v)
        have h2 : detHom Q _ (γ v) = 1 := Units.ext (by rw [detHom_val]; exact hγs v)
        rw [h1, h2, inv_one, mul_one]
  · rw [hδ v, if_neg hv, ← hγx v, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel_right,
      hσx v]

/-- **Cassels, Theorem 7.1** (Ch. 11, p. 227), lattice form over a number field: *let $f$ be a classically integral
form over $\mathbb Z$ in $n \ge 4$ variables, and suppose that $a \in \mathbb Z$, $a \ne 0$, is representable primitively
by $f$ over every $\mathbb Z_p$ (including $p = \infty$). Then $a$ is primitively representable over $\mathbb Z$ by some
form in the spinor genus of $f$.* Here $f$ is a lattice `L` on the regular space $(F^n, Q)$ (any lattice: the
classical integrality of $f$ is not used), "over $\mathbb Z_p$" is `hloc` (a primitive vector $y$ of $L_\mathfrak p$
with $Q(y) = a$, `LocPrimitive`) at the finite primes and `hinf` (representation over the completion) at the infinite
places, and the conclusion is a lattice $M$ in the proper spinor genus of $L$ (Cassels' spinor genus) with a primitive
vector $x$ (`LatPrimitive`), $Q(x) = a$. *Proof:* module docstring. -/
@[kb "cassels1978" "Ch. 11, Thm. 7.1, p. 227 (lattice form, over a number field)"]
theorem exists_sameProperSpinorGenus_primitive (hQ : Q.Nondegenerate) (hn : 4 ≤ n) (L : Lat F n) {a : F}
    (ha : a ≠ 0) (hinf : ∀ w : InfinitePlace F, Q.RepresentsIn w.Completion a)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ y, LocPrimitive v (loc v L.1) y ∧
      Q.evalIn (v.adicCompletion F) y = algebraMap F _ a) :
    ∃ M : Lat F n, SameProperSpinorGenus Q L M ∧ ∃ x, LatPrimitive M.1 x ∧ Q.evalIn F x = a := by
  classical
  -- `a = Q(x)` over `F`, by the Hasse principle
  obtain ⟨x, hxa⟩ : Q.RepresentsIn F a := by
    rw [represents_iff_everywhere_nf Q hQ a ha]
    intro w
    cases w with
    | infinite w => exact hinf w
    | finite v =>
      obtain ⟨y, -, hy⟩ := hloc v
      exact ⟨y, hy⟩
  have hxa' : Q.evalIn F x = a := by simpa using hxa
  have hx0 : Q.evalIn F x ≠ 0 := hxa' ▸ ha
  have hxne : x ≠ 0 := by
    rintro rfl; apply hx0; simp [QuadForm.evalIn]
  choose y hyp hya using hloc
  obtain ⟨δ, hδk, hδ⟩ := exists_spinorKernelAf_move Q hQ hn hx0
    (fun v => LocPrimitive v (loc v L.1) (locVec v x)) (eventually_locPrimitive L.2 hxne) y
    (fun v => by rw [hya v, hxa'])
  refine ⟨latSMul Q δ L, ⟨δ, Subgroup.mem_sup_right hδk, rfl⟩, x, ?_, hxa'⟩
  apply latPrimitive_of_forall_loc (latSMul Q δ L).2
  intro v
  rw [loc_latSMul]
  by_cases hv : LocPrimitive v (loc v L.1) (locVec v x)
  · rw [(hδ v).1 hv, OneMemClass.coe_one, locAct_one]
    exact hv
  · rw [← (hδ v).2 hv]
    exact (hyp v).locAct _

/-- **Representations by the proper spinor genus** (the argument of Theorem 7.1 without primitivity; used for the
Corollary to Theorem 8.3 when $n \ge 4$): if $n \ge 4$, $c = Q(x) \ne 0$ with $x \in V$, and $c$ is represented by
$L_\mathfrak p$ at every prime, then $x$ lies in some lattice $M$ of the proper spinor genus of $L$. -/
theorem exists_sameProperSpinorGenus_mem (hQ : Q.Nondegenerate) (hn : 4 ≤ n) (L : Lat F n) {c : F} (hc : c ≠ 0)
    {x : Fin n → F} (hx : Q.evalIn F x = c)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ y ∈ loc v L.1,
      Q.evalIn (v.adicCompletion F) y = algebraMap F (v.adicCompletion F) c) :
    ∃ M : Lat F n, SameProperSpinorGenus Q L M ∧ x ∈ M.1 := by
  classical
  have hx0 : Q.evalIn F x ≠ 0 := hx ▸ hc
  have hxne : x ≠ 0 := by
    rintro rfl; apply hx0; simp [QuadForm.evalIn]
  choose y hyL hya using hloc
  obtain ⟨δ, hδk, hδ⟩ := exists_spinorKernelAf_move Q hQ hn hx0
    (fun v => locVec v x ∈ loc v L.1)
    ((eventually_locPrimitive L.2 hxne).mono fun v hv => hv.1) y (fun v => by rw [hya v, hx])
  refine ⟨latSMul Q δ L, ⟨δ, Subgroup.mem_sup_right hδk, rfl⟩, ?_⟩
  rw [mem_iff_forall_loc (latSMul Q δ L).2]
  intro v
  rw [loc_latSMul]
  by_cases hv : locVec v x ∈ loc v L.1
  · rw [(hδ v).1 hv, OneMemClass.coe_one, locAct_one]
    exact hv
  · exact ⟨y v, hyL v, (hδ v).2 hv⟩

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion InfinitePlace.Completion.instAlgebra in
/-- **Cassels, Theorem 7.1** (Ch. 11, p. 227), over $\mathbb Q$ (Cassels' setting): `exists_sameProperSpinorGenus_primitive`
for $F = \mathbb Q$; `hinf` is primitive representability over $\mathbb Z_\infty = \mathbb R$ (for the real place
"primitively" is no condition). -/
@[kb "cassels1978" "Ch. 11, Thm. 7.1, p. 227 (lattice form)"]
theorem exists_sameProperSpinorGenus_primitive_rat (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (L : Lat ℚ n) {a : ℚ} (ha : a ≠ 0) (hinf : ∀ w : InfinitePlace ℚ, Q.RepresentsIn w.Completion a)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ y, LocPrimitive v (loc v L.1) y ∧
      Q.evalIn (v.adicCompletion ℚ) y = algebraMap ℚ _ a) :
    ∃ M : Lat ℚ n, SameProperSpinorGenus Q L M ∧ ∃ x, LatPrimitive M.1 x ∧ Q.evalIn ℚ x = a :=
  exists_sameProperSpinorGenus_primitive Q hQ hn L ha hinf hloc

end Main

end QuadFormsKB.Lattices
