/-
# Conway–Sloane, Ch. 15, §7.1–7.2, Theorem 9: classification of forms over $\mathbb Z_p$, $p$ odd

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.1–7.2, Thm. 9, p. 379
(bibliography key `conwaysloane1999`). For odd $p$ the $p$-adic symbol of an integral form
$f = \bigoplus_q qf_q$ ($q = p^k$, $f_q$ a unit form) records, for each scale $q$, the dimension $n_q = \dim f_q$ and
the sign $\varepsilon_q = \left(\frac{\det f_q}{p}\right)$. **Theorem 9**: for $p \ne 2$, two such forms are
$\mathbb Z_p$-equivalent iff they have the same $p$-adic symbol.

**Formalization.** A form is a matrix $F \in M_n(\mathbb Q_p)$; $\mathbb Z_p$-equivalence is `ZpEquiv`
(Cassels' `Ch8/Canonical.lean`: $G = T^{t}FT$, $T \in \mathrm{GL}_n(\mathbb Z_p)$). At odd $p$ every Jordan constituent
diagonalizes (Conway–Sloane, Thm. 2), so a Jordan decomposition is recorded as a $\mathbb Z_p$-equivalence of $F$ with a
diagonal matrix $\operatorname{diag}(p^{z_i}u_i)$, $z_i \in \mathbb N$, $u_i$ $p$-adic units (`IsOddSymbolOf`). The symbol
of this diagonal form (`oddSymbolOfDiag`) has, at scale $p^k$, the dimension $n_{p^k} = \#\{i : z_i = k\}$ and the sign
$\varepsilon_{p^k} = +$ iff $\prod_{z_i = k}u_i$ is a square in $\mathbb Q_p$ (for a unit at an odd prime, a square
means a quadratic residue, so this is the Legendre symbol $\left(\frac{\det f_q}{p}\right)$).

**Defines**
* `oddSymbolOfDiag`: the symbol of a diagonal form $\operatorname{diag}(p^{z_i}u_i)$;
* `IsOddSymbolOf`: $\sigma$ is the $p$-adic symbol of $F$ (via a diagonal Jordan decomposition).

**Proves** (all for $p \ne 2$)
* `exists_isOddSymbolOf`: every integral, symmetric, non-singular $F$ has a $p$-adic symbol (from Cassels'
  canonical forms, Ch. 8, Thm. 3.1);
* `oddSymbol_eq_of_zpEquiv`, `oddSymbol_unique`: the symbol is an invariant of the $\mathbb Z_p$-equivalence class
  (well defined);
* `zpEquiv_of_oddSymbol_eq`: equal symbols give $\mathbb Z_p$-equivalent forms;
* `theorem9`: **Theorem 9**, $F \sim_{\mathbb Z_p} G \iff$ same $p$-adic symbol.

Invariance rests on the uniqueness of Jordan types (`generic_unique`, `Cassels/Ch8/CanonicalUnique.lean`); completeness
on Cassels' existence and uniqueness of canonical forms.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Thm31
import QuadFormsKB.Literature.ConwaySloane.Symbol

namespace QuadFormsKB.ConwaySloane

open Matrix QuadFormsKB.Cassels

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

open scoped Classical in
/-- The $p$-adic symbol (odd $p$) of the diagonal form $\operatorname{diag}(p^{z_i}u_i)$ with unit entries $u_i$:
at scale $q = p^k$ the dimension is $n_q = \#\{i : z_i = k\}$ and the sign is $\varepsilon_q = +$ iff
$\prod_{z_i = k}u_i$ is a square in $\mathbb Q_p$. For $p$-adic units at an odd prime, being a square is being a
quadratic residue, so this is $\varepsilon_q = \left(\frac{\det f_q}{p}\right)$ for the unit form
$f_q = \operatorname{diag}(u_i)_{z_i = k}$ (Conway–Sloane, §7.2, p. 379). -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.2, Thm. 9, p. 379 (the symbol of a diagonal form)"]
noncomputable def oddSymbolOfDiag (p : ℕ) [Fact p.Prime] (z : Fin n → ℕ) (u : Fin n → ℚ_[p]) : OddSymbol :=
  fun k => ⟨Fintype.card {i // z i = k}, if IsSquare (∏ i : {i // z i = k}, u i) then .plus else .minus⟩

/-- $\sigma$ is the $p$-adic symbol of the form $F \in M_n(\mathbb Q_p)$: $F$ is $\mathbb Z_p$-equivalent to a diagonal
form $\operatorname{diag}(p^{z_i}u_i)$ with exponents $z_i \in \mathbb N$ and unit entries $\lVert u_i\rVert_p = 1$
(a diagonal Jordan decomposition; at odd $p$ every Jordan constituent diagonalizes, Conway–Sloane Thm. 2), and
$\sigma$ is the symbol of that diagonal form. -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.2, Thm. 9, p. 379 (the p-adic symbol of a form)"]
def IsOddSymbolOf (p : ℕ) [Fact p.Prime] (F : Matrix (Fin n) (Fin n) ℚ_[p]) (σ : OddSymbol) : Prop :=
  ∃ z : Fin n → ℕ, ∃ u : Fin n → ℚ_[p], (∀ i, ‖u i‖ = 1) ∧
    ZpEquiv F (Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z i) * u i) ∧ σ = oddSymbolOfDiag p z u

/-! ### Auxiliary facts -/

/-- There is a quadratic non-residue unit in $\mathbb Q_p$ for odd $p$. -/
theorem exists_nonsq_unit (hp2 : p ≠ 2) : ∃ r : ℚ_[p], ‖r‖ = 1 ∧ ¬ IsSquare r := by
  have : Fact (ringChar (ZMod p) ≠ 2) := ⟨by rwa [ZMod.ringChar_zmod_n]⟩
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨r, hr⟩ : ∃ r : ℤ_[p], PadicInt.toZMod r = a := ⟨(a.val : ℤ_[p]), by simp⟩
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by simp [h]⟩
  have hru : IsUnit r := by
    by_contra hn
    apply ha0
    rw [← hr, ← RingHom.mem_ker, PadicInt.ker_toZMod]
    exact (IsLocalRing.mem_maximalIdeal _).2 hn
  refine ⟨(r : ℚ_[p]), PadicInt.isUnit_iff.1 hru, ?_⟩
  rintro ⟨x, hx⟩
  have hn : ‖x‖ = 1 := by
    have h1 : ‖(r : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.1 hru
    rw [hx, norm_mul] at h1
    nlinarith [norm_nonneg x]
  let y : ℤ_[p] := ⟨x, (PadicInt.mem_subring_iff p).2 hn.le⟩
  have hy : r = y * y := Subtype.ext hx
  apply ha
  exact ⟨PadicInt.toZMod y, by rw [← hr, hy, map_mul]⟩

/-- If $A$ is integral and $B = T^{t}AT$ with $T \in \mathrm{GL}_n(\mathbb Z_p)$, then $B$ is integral. -/
theorem integral_of_zpEquiv {A B : Matrix (Fin n) (Fin n) ℚ_[p]} (h : ZpEquiv A B)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) : ∀ i j, ‖B i j‖ ≤ 1 := by
  obtain ⟨T, rfl⟩ := h
  let A' : Matrix (Fin n) (Fin n) ℤ_[p] := fun i j => ⟨A i j, (PadicInt.mem_subring_iff p).2 (hA i j)⟩
  have hA' : A = A'.map PadicInt.Coe.ringHom := rfl
  have : (T.val.map PadicInt.Coe.ringHom)ᵀ * A * T.val.map PadicInt.Coe.ringHom =
      (T.valᵀ * A' * T.val).map PadicInt.Coe.ringHom := by
    rw [hA']
    simp [Matrix.map_mul, Matrix.transpose_map]
  intro i j
  rw [this]
  exact PadicInt.norm_le_one _

/-- A diagonal entry $p^zu$ ($u$ a unit) of norm at most $1$ has $z \ge 0$. -/
theorem nonneg_of_norm_le {z : ℤ} {u : ℚ_[p]} (hu : ‖u‖ = 1) (h : ‖(p : ℚ_[p]) ^ z * u‖ ≤ 1) : 0 ≤ z := by
  rw [norm_mul, hu, mul_one, Padic.norm_p_zpow] at h
  by_contra hz
  push Not at hz
  have : (1 : ℝ) < (p : ℝ) ^ (-z) := one_lt_zpow₀ (by exact_mod_cast hp.out.one_lt) (by omega)
  linarith

/-- The diagonal entries $p^zu$ ($z \in \mathbb N$, $u$ a unit) are integral. -/
theorem norm_diag_le {z : ℕ} {u : ℚ_[p]} (hu : ‖u‖ = 1) : ‖(p : ℚ_[p]) ^ z * u‖ ≤ 1 := by
  rw [norm_mul, hu, mul_one, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le

/-- A diagonal form $\operatorname{diag}(p^{z_i}u_i)$ with $z_i \in \mathbb N$ and unit $u_i$ is integral. -/
theorem diag_integral{z : Fin n → ℕ} {u : Fin n → ℚ_[p]} (hu : ∀ i, ‖u i‖ = 1) :
    ∀ i j, ‖(Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z i) * u i) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact norm_diag_le (hu i)
  · simp

/-- The product of the $p^{z_i}u_i$ over a block of equal exponent $k$. -/
theorem blockprod (z : Fin n → ℕ) (u : Fin n → ℚ_[p]) (k : ℕ) :
    ∏ i : {i // z i = k}, ((p : ℚ_[p]) ^ (z i) * u i) =
      ((p : ℚ_[p]) ^ k) ^ (Fintype.card {i // z i = k}) * ∏ i : {i // z i = k}, u i := by
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_congr rfl (fun i _ => by rw [i.2]), Finset.prod_const, Finset.card_univ]

/-- Transport of the size of a block between `ℤ`-valued and `ℕ`-valued exponents. -/
theorem card_cast(z : Fin n → ℕ) (k : ℕ) :
    Fintype.card {i // (z i : ℤ) = (k : ℤ)} = Fintype.card {i // z i = k} :=
  Fintype.card_congr (Equiv.subtypeEquivRight fun i => by simp)

/-- Transport of a block product between `ℤ`-valued and `ℕ`-valued exponents. -/
theorem prod_cast(z : Fin n → ℕ) (k : ℕ) (f : Fin n → ℚ_[p]) :
    ∏ i : {i // (z i : ℤ) = (k : ℤ)}, f i = ∏ i : {i // z i = k}, f i :=
  Fintype.prod_equiv (Equiv.subtypeEquivRight fun i => by simp) _ _ (fun _ => rfl)

/-- Multiplying by a nonzero square does not change whether an element is a square. -/
theorem isSquare_iff_of_eq{P P' ε : ℚ_[p]} (hε : ε ≠ 0) (h : P = ε ^ 2 * P') : IsSquare P ↔ IsSquare P' := by
  subst h
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s / ε, ?_⟩
    field_simp
    linear_combination hs
  · rintro ⟨s, hs⟩
    exact ⟨ε * s, by rw [hs]; ring⟩

/-- The symbols of two diagonal forms agree at scale $p^k$ if the dimensions agree and the squareness of the unit
parts agrees. -/
theorem oddSymbolOfDiag_congr{z z' : Fin n → ℕ} {u u' : Fin n → ℚ_[p]} {k : ℕ}
    (hc : Fintype.card {i // z i = k} = Fintype.card {i // z' i = k})
    (hs : IsSquare (∏ i : {i // z i = k}, u i) ↔ IsSquare (∏ i : {i // z' i = k}, u' i)) :
    oddSymbolOfDiag p z u k = oddSymbolOfDiag p z' u' k := by
  classical
  unfold oddSymbolOfDiag
  rw [hc]
  by_cases a : IsSquare (∏ i : {i // z i = k}, u i)
  · simp [a, hs.1 a]
  · simp [a, mt hs.2 a]

/-- Equal symbols at scale $p^k$ give equal dimensions and equal squareness of the unit parts. -/
theorem dim_sign_of_eq{z z' : Fin n → ℕ} {u u' : Fin n → ℚ_[p]} {k : ℕ}
    (h : oddSymbolOfDiag p z u k = oddSymbolOfDiag p z' u' k) :
    Fintype.card {i // z i = k} = Fintype.card {i // z' i = k} ∧
      (IsSquare (∏ i : {i // z i = k}, u i) ↔ IsSquare (∏ i : {i // z' i = k}, u' i)) := by
  unfold oddSymbolOfDiag at h
  have h1 := congrArg OddFactor.dim h
  have h2 := congrArg OddFactor.sign h
  simp only at h1 h2
  refine ⟨h1, ?_⟩
  by_cases a : IsSquare (∏ i : {i // z i = k}, u i) <;> by_cases b : IsSquare (∏ i : {i // z' i = k}, u' i) <;>
    simp_all

/-- The finitely many values of an integer-valued function, in strictly increasing order. -/
theorem exists_enum(z : Fin n → ℤ) :
    ∃ (t : ℕ) (Zs : Fin t → ℤ), StrictMono Zs ∧ (∀ i, ∃ j, z i = Zs j) ∧ ∀ j, ∃ i, z i = Zs j := by
  classical
  let S := Finset.univ.image z
  refine ⟨S.card, S.orderEmbOfFin rfl, (S.orderEmbOfFin rfl).strictMono, fun i => ?_, fun j => ?_⟩
  · have : z i ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact_mod_cast Finset.mem_image_of_mem _ (Finset.mem_univ i)
    obtain ⟨j, hj⟩ := this
    exact ⟨j, hj.symm⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (Finset.orderEmbOfFin_mem S rfl j)
    exact ⟨i, hi⟩

/-- A $\mathbb Z_p$-equivalence gives an isometry of $\mathbb Q_p^n$ carrying $\mathbb Z_p^n$ onto itself. -/
theorem iso_of_zpEquiv {A B : Matrix (Fin n) (Fin n) ℚ_[p]} (h : ZpEquiv A B) :
    ∃ σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]), (∀ x, qfForm A (σ x) = qfForm B x) ∧
      OMeara.latMap σ (zpLat p n) = zpLat p n := by
  obtain ⟨T, hT⟩ := h
  set W : Matrix (Fin n) (Fin n) ℚ_[p] := T.val.map PadicInt.Coe.ringHom with hW
  set W' : Matrix (Fin n) (Fin n) ℚ_[p] := (T⁻¹).val.map PadicInt.Coe.ringHom with hW'
  have hWW' : W * W' = 1 := by
    rw [hW, hW', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hW'W : W' * W = 1 := by
    rw [hW, hW', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  let σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]) :=
    LinearEquiv.ofLinearMap (Matrix.mulVecLin W) (Matrix.mulVecLin W')
      (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, hWW'])
      (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, hW'W])
  have hσx : ∀ x, σ x = W *ᵥ x := fun x => rfl
  refine ⟨σ, fun x => ?_, ?_⟩
  · rw [qfForm_apply, qfForm_apply, ← hT, qf_conj', hσx]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_zpLat.2 (isIntVec_mulVec T.val (mem_zpLat.1 hx))
    · intro hy
      refine ⟨σ.symm y, mem_zpLat.2 (isIntVec_mulVec (T⁻¹).val (mem_zpLat.1 hy)), ?_⟩
      simp

/-! ### Invariance of the symbol -/

/-- If the scale $p^k$ occurs in the first diagonal form, then the symbols of two $\mathbb Z_p$-equivalent diagonal
forms agree at $p^k$. -/
theorem symbol_eq_of_attained (hp2 : p ≠ 2) {z z' : Fin n → ℕ} {u u' : Fin n → ℚ_[p]}
    (hu : ∀ i, ‖u i‖ = 1) (hu' : ∀ i, ‖u' i‖ = 1)
    (hE : ZpEquiv (Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z i) * u i)
      (Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z' i) * u' i))
    {k : ℕ} (hk : ∃ i, z i = k) : oddSymbolOfDiag p z u k = oddSymbolOfDiag p z' u' k := by
  classical
  obtain ⟨σ, hσ, hσM⟩ := iso_of_zpEquiv hE
  obtain ⟨t, Zs, hZ, hcov, hne⟩ := exists_enum (fun i => (z i : ℤ))
  obtain ⟨t', Zs', hZ', hcov', hne'⟩ := exists_enum (fun i => (z' i : ℤ))
  obtain ⟨htt, hall⟩ := generic_unique hp2 (fun i => (p : ℚ_[p]) ^ (z i) * u i) u
    (fun i => (p : ℚ_[p]) ^ (z' i) * u' i) u' (fun i => (z i : ℤ)) (fun i => (z' i : ℤ)) hu
    (fun i => by simp [zpow_natCast]) hu' (fun i => by simp [zpow_natCast]) Zs hZ hcov hne
    Zs' hZ' hcov' hne' σ hσ hσM
  obtain ⟨i0, hi0⟩ := hk
  obtain ⟨j, hj⟩ := hcov i0
  obtain ⟨hZj, hcard, ε, hε, hprod⟩ := hall j
  have h1 : Zs j = (k : ℤ) := by rw [← hj, hi0]
  have h2 : Zs' (Fin.cast htt j) = (k : ℤ) := by rw [← hZj, h1]
  rw [h1, h2] at hcard hprod
  rw [card_cast] at hcard
  rw [card_cast] at hcard
  rw [prod_cast z k (fun i => (p : ℚ_[p]) ^ (z i) * u i),
    prod_cast z' k (fun i => (p : ℚ_[p]) ^ (z' i) * u' i), blockprod, blockprod, ← hcard] at hprod
  have hpk : ((p : ℚ_[p]) ^ k) ^ (Fintype.card {i // z i = k}) ≠ 0 := by
    have : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    positivity
  have hε0 : (ε : ℚ_[p]) ≠ 0 := fun h => hε.ne_zero (Subtype.ext h)
  have hP : ∏ i : {i // z i = k}, u i = (ε : ℚ_[p]) ^ 2 * ∏ i : {i // z' i = k}, u' i := by
    apply mul_left_cancel₀ hpk
    linear_combination hprod
  exact oddSymbolOfDiag_congr hcard (isSquare_iff_of_eq hε0 hP)

/-- **Invariance of the $p$-adic symbol** ($p \ne 2$): $\mathbb Z_p$-equivalent forms have the same $p$-adic symbol. -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.2, Thm. 9, p. 379 (invariance of the symbol)"]
theorem oddSymbol_eq_of_zpEquiv (hp2 : p ≠ 2) {F G : Matrix (Fin n) (Fin n) ℚ_[p]} {σ τ : OddSymbol}
    (h : ZpEquiv F G) (hF : IsOddSymbolOf p F σ) (hG : IsOddSymbolOf p G τ) : σ = τ := by
  obtain ⟨z, u, hu, hFe, rfl⟩ := hF
  obtain ⟨z', u', hu', hGe, rfl⟩ := hG
  have hE := hFe.symm.trans (h.trans hGe)
  funext k
  by_cases hk : ∃ i, z i = k
  · exact symbol_eq_of_attained hp2 hu hu' hE hk
  by_cases hk' : ∃ i, z' i = k
  · exact (symbol_eq_of_attained hp2 hu' hu hE.symm hk').symm
  have e1 : IsEmpty {i // z i = k} := ⟨fun x => hk ⟨x.1, x.2⟩⟩
  have e2 : IsEmpty {i // z' i = k} := ⟨fun x => hk' ⟨x.1, x.2⟩⟩
  exact oddSymbolOfDiag_congr (by simp) (by simp)

/-- **The $p$-adic symbol is well defined** ($p \ne 2$): a form has at most one $p$-adic symbol. -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.2, Thm. 9, p. 379 (uniqueness of the symbol of a form)"]
theorem oddSymbol_unique (hp2 : p ≠ 2) {F : Matrix (Fin n) (Fin n) ℚ_[p]} {σ τ : OddSymbol}
    (hF : IsOddSymbolOf p F σ) (hG : IsOddSymbolOf p F τ) : σ = τ :=
  oddSymbol_eq_of_zpEquiv hp2 (ZpEquiv.refl F) hF hG

/-! ### Existence of the symbol and completeness -/

/-- The data of a canonical form read as a diagonal form with exponents in $\mathbb N$: if the canonical matrix is
integral, it is $\operatorname{diag}(p^{z_i}u_i)$ with $z_i \in \mathbb N$ and unit $u_i$, the exponents occurring
are exactly the exponents $e(j)$ of the blocks, and block $j$ has $m_j$ entries of exponent $e(j)$ whose unit parts
multiply to $r^{\varepsilon_j}$. -/
theorem canon_nat {r : ℚ_[p]} (hr1 : ‖r‖ = 1) {D : List CanonBlock} (hD : IsCanon D)
    (h : (canonEntries p r D).length = n) (hint : ∀ i j, ‖canonMat r D h i j‖ ≤ 1) :
    ∃ (z : Fin n → ℕ) (u : Fin n → ℚ_[p]),
      canonMat r D h = Matrix.diagonal (fun i => (p : ℚ_[p]) ^ (z i) * u i) ∧ (∀ i, ‖u i‖ = 1) ∧
      (∀ i, ∃ j : Fin D.length, (z i : ℤ) = D[j].e) ∧
      (∀ j : Fin D.length, ∃ k : ℕ, (k : ℤ) = D[j].e ∧ Fintype.card {i // z i = k} = D[j].m ∧
        ∏ i : {i // z i = k}, u i = r ^ (D[j].ε : ℕ)) := by
  obtain ⟨zZ, u, hA, hu, hcov, hne, hblk⟩ := canon_data hr1 hD h
  have hnn : ∀ i, 0 ≤ zZ i := by
    intro i
    have := hint i i
    rw [hA, Matrix.diagonal_apply_eq] at this
    exact nonneg_of_norm_le (hu i) this
  obtain ⟨z, hz⟩ : ∃ z : Fin n → ℕ, zZ = fun i => (z i : ℤ) :=
    ⟨fun i => (zZ i).toNat, funext fun i => (Int.toNat_of_nonneg (hnn i)).symm⟩
  subst hz
  refine ⟨z, u, ?_, hu, hcov, fun j => ?_⟩
  · rw [hA]
    congr 1
    funext i
    simp [zpow_natCast]
  · obtain ⟨i0, hi0⟩ := hne j
    have hi0' : (z i0 : ℤ) = D[j].e := hi0
    refine ⟨z i0, hi0', ?_⟩
    obtain ⟨hc, hpr⟩ := hblk j
    beta_reduce at hc hpr
    rw [← hi0'] at hc hpr
    rw [card_cast] at hc
    simp only [zpow_natCast] at hpr
    rw [prod_cast z (z i0) (fun i => (p : ℚ_[p]) ^ (z i) * u i), blockprod, hc] at hpr
    refine ⟨hc, ?_⟩
    have hpk : ((p : ℚ_[p]) ^ (z i0)) ^ D[j].m ≠ 0 := by
      have : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      positivity
    exact mul_left_cancel₀ hpk hpr

/-- Two canonical forms (lists of blocks) with the same blocks are equal. -/
theorem canon_eq_of_mem {D D' : List CanonBlock} (hD : IsCanon D) (hD' : IsCanon D')
    (h : ∀ b, b ∈ D ↔ b ∈ D') : D = D' := by
  have : IsTrans CanonBlock (fun a b => a.e < b.e) := ⟨fun a b c h1 h2 => h1.trans h2⟩
  have p1 : D.Pairwise (fun a b => a.e < b.e) := List.isChain_iff_pairwise.1 hD.1
  have p2 : D'.Pairwise (fun a b => a.e < b.e) := List.isChain_iff_pairwise.1 hD'.1
  have nd : D.Nodup := p1.imp (fun {a b} hab h => hab.ne (congrArg CanonBlock.e h))
  have nd' : D'.Nodup := p2.imp (fun {a b} hab h => hab.ne (congrArg CanonBlock.e h))
  exact ((List.perm_ext_iff_of_nodup nd nd').2 h).eq_of_pairwise
    (fun a _ b _ h1 h2 => (lt_asymm h1 h2).elim) p1 p2

/-- $r^{\varepsilon}$ ($\varepsilon \in \{0,1\}$, $r$ a non-residue) is a square iff $\varepsilon = 0$. -/
theorem isSquare_r_pow{r : ℚ_[p]} (hr : ¬ IsSquare r) (ε : Fin 2) :
    IsSquare (r ^ (ε : ℕ)) ↔ (ε : ℕ) = 0 := by
  rcases ε with ⟨_ | _ | e, he⟩
  · simp
  · simp [hr]
  · omega

/-- Extensionality for canonical blocks. -/
theorem canonBlock_ext{a b : CanonBlock} (h1 : a.e = b.e) (h2 : a.ε = b.ε) (h3 : a.m = b.m) : a = b := by
  cases a
  cases b
  simp_all

/-- Equal symbols force the same blocks: every block of $D$ is a block of $D'$. -/
theorem mem_of_symbol {r : ℚ_[p]} (hr : ¬ IsSquare r) {D D' : List CanonBlock} (hD : IsCanon D)
    {z z' : Fin n → ℕ} {u u' : Fin n → ℚ_[p]}
    (hcov' : ∀ i, ∃ j : Fin D'.length, (z' i : ℤ) = D'[j].e)
    (hblk : ∀ j : Fin D.length, ∃ k : ℕ, (k : ℤ) = D[j].e ∧ Fintype.card {i // z i = k} = D[j].m ∧
      ∏ i : {i // z i = k}, u i = r ^ (D[j].ε : ℕ))
    (hblk' : ∀ j : Fin D'.length, ∃ k : ℕ, (k : ℤ) = D'[j].e ∧ Fintype.card {i // z' i = k} = D'[j].m ∧
      ∏ i : {i // z' i = k}, u' i = r ^ (D'[j].ε : ℕ))
    (hs : oddSymbolOfDiag p z u = oddSymbolOfDiag p z' u') : ∀ b, b ∈ D → b ∈ D' := by
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb
  obtain ⟨k, hk, hc, hpr⟩ := hblk ⟨j, hj⟩
  have hc2 : Fintype.card {i // z i = k} = D[j].m := hc
  have hk2 : (k : ℤ) = D[j].e := hk
  have hpr2 : ∏ i : {i // z i = k}, u i = r ^ (D[j].ε : ℕ) := hpr
  obtain ⟨hcard, hsq⟩ := dim_sign_of_eq (congrFun hs k)
  have hm : 1 ≤ D[j].m := hD.2 _ (List.getElem_mem hj)
  have hpos : 0 < Fintype.card {i // z' i = k} := by omega
  obtain ⟨⟨i, hi⟩⟩ := Fintype.card_pos_iff.1 hpos
  obtain ⟨j', hj'⟩ := hcov' i
  obtain ⟨k', hk', hc', hpr'⟩ := hblk' j'
  have hkk : k' = k := by
    have : (k' : ℤ) = k := by rw [hk', ← hj', hi]
    exact_mod_cast this
  rw [hkk] at hk' hc' hpr'
  refine List.mem_iff_getElem.2 ⟨j', j'.2, canonBlock_ext ?_ ?_ ?_⟩
  · have e2 : (k : ℤ) = D'[j'].e := hk'
    exact (e2.symm.trans hk2)
  · have hsq' : IsSquare (r ^ (D[j].ε : ℕ)) ↔ IsSquare (r ^ (D'[j'].ε : ℕ)) := by
      rwa [hpr2, hpr'] at hsq
    rw [isSquare_r_pow hr, isSquare_r_pow hr] at hsq'
    have := D[j].ε.isLt
    have := D'[j'].ε.isLt
    have hε : D[j].ε = D'[j'].ε := Fin.ext (by omega)
    exact hε.symm
  · have e3 : Fintype.card {i // z' i = k} = D'[j'].m := hc'
    exact (e3.symm.trans (hcard.symm.trans hc2))

/-- From a diagonal Jordan decomposition to a canonical form with the same symbol and block data. -/
theorem canon_of_isOddSymbolOf (hp2 : p ≠ 2) {r : ℚ_[p]} (hr1 : ‖r‖ = 1) (hr : ¬ IsSquare r)
    {F : Matrix (Fin n) (Fin n) ℚ_[p]} {σ : OddSymbol} (hF : IsOddSymbolOf p F σ) :
    ∃ D : List CanonBlock, IsCanon D ∧ ∃ h : (canonEntries p r D).length = n,
      ZpEquiv F (canonMat r D h) ∧ ∃ (z : Fin n → ℕ) (u : Fin n → ℚ_[p]),
        (∀ i, ‖u i‖ = 1) ∧ (∀ i, ∃ j : Fin D.length, (z i : ℤ) = D[j].e) ∧
        (∀ j : Fin D.length, ∃ k : ℕ, (k : ℤ) = D[j].e ∧ Fintype.card {i // z i = k} = D[j].m ∧
          ∏ i : {i // z i = k}, u i = r ^ (D[j].ε : ℕ)) ∧ σ = oddSymbolOfDiag p z u := by
  obtain ⟨z, u, hu, hFe, rfl⟩ := hF
  have hAT : (Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z i) * u i)ᵀ =
      Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z i) * u i := Matrix.diagonal_transpose _
  have hdet : (Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z i) * u i).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero
      (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) (norm_pos_iff.1 (by rw [hu i]; exact one_pos))
  obtain ⟨D, hD, h, hAD⟩ := exists_canonical hp2 hr1 hr _ hAT hdet
  have hint := integral_of_zpEquiv hAD (diag_integral hu)
  obtain ⟨z', u', hA', hu', hcov, hblk⟩ := canon_nat hr1 hD h hint
  refine ⟨D, hD, h, hFe.trans hAD, z', u', hu', hcov, hblk, ?_⟩
  exact oddSymbol_eq_of_zpEquiv hp2 (hFe.trans hAD) ⟨z, u, hu, hFe, rfl⟩
    ⟨z', u', hu', by rw [hA']; exact ZpEquiv.refl _, rfl⟩

/-- **Existence of the $p$-adic symbol** ($p \ne 2$): every integral, symmetric, non-singular form over $\mathbb Z_p$
has a $p$-adic symbol (Conway–Sloane, §7.1–7.2, p. 379; via the canonical forms of Cassels, Ch. 8, Thm. 3.1). -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.2, Thm. 9, p. 379 (existence of the symbol)"]
theorem exists_isOddSymbolOf (hp2 : p ≠ 2) {F : Matrix (Fin n) (Fin n) ℚ_[p]} (hF : Fᵀ = F)
    (hdet : F.det ≠ 0) (hint : ∀ i j, ‖F i j‖ ≤ 1) : ∃ σ : OddSymbol, IsOddSymbolOf p F σ := by
  obtain ⟨r, hr1, hr⟩ := exists_nonsq_unit hp2
  obtain ⟨D, hD, h, hFD⟩ := exists_canonical hp2 hr1 hr F hF hdet
  obtain ⟨z, u, hA, hu, -, -⟩ := canon_nat hr1 hD h (integral_of_zpEquiv hFD hint)
  exact ⟨_, z, u, hu, by rw [← hA]; exact hFD, rfl⟩

/-- **Completeness of the $p$-adic symbol** ($p \ne 2$): forms with the same $p$-adic symbol are
$\mathbb Z_p$-equivalent. -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.2, Thm. 9, p. 379 (equal symbols imply equivalence)"]
theorem zpEquiv_of_oddSymbol_eq (hp2 : p ≠ 2) {F G : Matrix (Fin n) (Fin n) ℚ_[p]} {σ : OddSymbol}
    (hF : IsOddSymbolOf p F σ) (hG : IsOddSymbolOf p G σ) : ZpEquiv F G := by
  obtain ⟨r, hr1, hr⟩ := exists_nonsq_unit hp2
  obtain ⟨D, hD, h, hFD, z, u, hu, hcov, hblk, hσ⟩ := canon_of_isOddSymbolOf hp2 hr1 hr hF
  obtain ⟨D', hD', h', hGD, z', u', hu', hcov', hblk', hσ'⟩ := canon_of_isOddSymbolOf hp2 hr1 hr hG
  have hs : oddSymbolOfDiag p z u = oddSymbolOfDiag p z' u' := hσ.symm.trans hσ'
  have hDD : D = D' := canon_eq_of_mem hD hD' fun b =>
    ⟨mem_of_symbol hr hD hcov' hblk hblk' hs b, mem_of_symbol hr hD' hcov hblk' hblk hs.symm b⟩
  subst hDD
  exact hFD.trans hGD.symm

/-- **Conway–Sloane, Ch. 15, Theorem 9**: *for $p \ne 2$, two forms $f$, $g$ over $\mathbb Z_p$ are $\mathbb Z_p$-equivalent
if and only if they have the same $p$-adic symbol* (the same $n_q$ and $\varepsilon_q$ for every $q = p^k$).
Here $F$, $G$ are symmetric and non-singular (integral, so that they have symbols: `exists_isOddSymbolOf`), and
$\sigma$, $\tau$ are their $p$-adic symbols (`IsOddSymbolOf`). Unconditional (no assumed inputs): proved from Cassels'
canonical forms (Ch. 8, Thm. 3.1) and the uniqueness of Jordan types. -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.2, Thm. 9, p. 379"]
theorem theorem9 (hp2 : p ≠ 2) {F G : Matrix (Fin n) (Fin n) ℚ_[p]} {σ τ : OddSymbol}
    (_hF : Fᵀ = F) (_hFd : F.det ≠ 0) (_hG : Gᵀ = G) (_hGd : G.det ≠ 0)
    (hσ : IsOddSymbolOf p F σ) (hτ : IsOddSymbolOf p G τ) : ZpEquiv F G ↔ σ = τ :=
  ⟨fun h => oddSymbol_eq_of_zpEquiv hp2 h hσ hτ,
    fun h => zpEquiv_of_oddSymbol_eq hp2 hσ (by rw [h]; exact hτ)⟩

end QuadFormsKB.ConwaySloane
