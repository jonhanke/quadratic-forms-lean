/-
# O'Meara §92: classes of lattices and the spaces of the Jordan components (Corollary 92:2a)

**Setting** (as in `Sec92.lean`): $R$ a complete discrete valuation ring with finite residue field, $2$ a unit of
$R$ (non-dyadic), fraction field $F$, a quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`. For a lattice
$L$, the space $FL$ is the $F$-span `span F L`; an isometry $FL \cong FK$ of spaces is `IsometricLat` over the ring
$F$ itself (an $F$-linear bijection preserving $Q$).

**Proves**
* `IsometricLat.span`: $L \cong K$ gives $FL \cong FK$;
* `sameDisc_of_isometric_span`: for $\mathfrak a$-modular $L$, $K$ of the same rank, $FL \cong FK$ gives
  $dL = dK$ in $F/\mathfrak u^2$;
* `cls_eq_iff_isometric_span` (**Corollary 92:2a**, p. 248): for lattices of the same Jordan type on $V$,
  $\operatorname{cls} L = \operatorname{cls} K$ if and only if $FL_i \cong FK_i$ for every $i$.
-/
import QuadFormsKB.Literature.OMeara.Sec92Jordan

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

omit [IsDiscreteValuationRing R] [Invertible (2 : F)] in
/-- A base of a lattice $L$ is an $F$-base of $FL$. -/
theorem exists_basis_span {L : Submodule R V} {ι : Type*} (b : Basis ι R L) :
    ∃ e : Basis ι F (span F (L : Set V)), ∀ i, (e i : V) = (b i : V) := by
  have hli : LinearIndependent F (fun i => (b i : V)) := by
    rw [← LinearIndependent.iff_fractionRing (R := R)]
    exact b.linearIndependent.map' L.subtype (ker_subtype L)
  have hsp : span F (Set.range fun i => (b i : V)) = span F (L : Set V) := by
    rw [← Submodule.span_span_of_tower R, span_basis_eq b]
  exact ⟨(Basis.span hli).map (LinearEquiv.ofEq _ _ hsp), fun i => by simp⟩

omit [IsDiscreteValuationRing R] [Invertible (2 : F)] in
/-- In a valuation ring: if $c^2 = w$ with $w$ a unit of $R$, then $c$ is a unit of $R$. -/
theorem exists_unit_of_sq_eq [ValuationRing R] {c : F} {w : R} (hw : IsUnit w) (h : c ^ 2 = algebraMap R F w) :
    ∃ r : R, IsUnit r ∧ c = algebraMap R F r := by
  rcases ValuationRing.isInteger_or_isInteger R c with ⟨r, hr⟩ | ⟨r, hr⟩
  · refine ⟨r, ?_, hr.symm⟩
    have : r ^ 2 = w := (IsFractionRing.injective R F) (by rw [map_pow, hr, h])
    exact (isUnit_pow_iff two_ne_zero).mp (this ▸ hw)
  · have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at h
      exact hw.ne_zero ((IsFractionRing.injective R F) (h.symm.trans (map_zero _).symm))
    have h1 : r ^ 2 * w = 1 := by
      apply IsFractionRing.injective R F
      rw [map_mul, map_pow, hr, ← h, map_one, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hc0)]
    have hru : IsUnit r := (isUnit_pow_iff two_ne_zero).mp (IsUnit.of_mul_eq_one _ h1)
    refine ⟨↑hru.unit⁻¹, Units.isUnit _, ?_⟩
    have : algebraMap R F (↑hru.unit⁻¹ : R) * algebraMap R F r = 1 := by
      rw [← map_mul, IsUnit.val_inv_mul, map_one]
    rw [hr] at this
    exact ((mul_inv_eq_one₀ hc0).mp this).symm

omit [Invertible (2 : F)] in
theorem gram_eq_of_isometricLat {L : Submodule R V} {K : Submodule R V'} {ι : Type*} [Invertible (2 : F)]
    (b : Basis ι R L) (f : L ≃ₗ[R] K) (hf : ∀ x : L, Q' (f x : V') = Q (x : V)) :
    gram Q' (fun i => ((b.map f) i : V')) = gram Q (fun i => (b i : V)) := by
  ext i j
  simp only [gram, Matrix.of_apply, Basis.map_apply]
  exact bil_eq_of_isometricLat Q Q' f hf _ _

/-- **Isometric lattices span isometric spaces**: $L \cong K$ gives $FL \cong FK$. -/
theorem IsometricLat.span {L : Submodule R V} {K : Submodule R V'} (h : IsometricLat Q Q' L K) (hL : L.FG) :
    IsometricLat (R := F) Q Q' (span F (L : Set V)) (span F (K : Set V')) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hL
  obtain ⟨e, he⟩ := exists_basis_span (F := F) b
  obtain ⟨e', he'⟩ := exists_basis_span (F := F) (b.map f)
  refine isometricLat_of_gram_eq (R := F) Q Q' e e' ?_
  have h1 : (fun i => (e i : V)) = fun i => (b i : V) := funext he
  have h2 : (fun i => (e' i : V')) = fun i => ((b.map f) i : V') := funext he'
  rw [h1, h2, gram_eq_of_isometricLat Q Q' b f hf]

/-- **Isometric spaces of modular lattices give equal discriminants** (the step $FL_i \cong FK_i \Rightarrow
dL_i = dK_i$ of 92:2a): if $L$ and $K$ are $\alpha$-modular of the same rank and $FL \cong FK$, then
$dL = dK$ in $F/\mathfrak u^2$. -/
theorem sameDisc_of_isometric_span {a : Submodule R F} {L : Submodule R V} {K : Submodule R V'} (hLfg : L.FG)
    (hKfg : K.FG) (hL : IsModular Q a L) (hK : IsModular Q' a K) (hrk : finrank R L = finrank R K)
    (h : IsometricLat (R := F) Q Q' (span F (L : Set V)) (span F (K : Set V'))) : SameDisc Q Q' L K := by
  classical
  have := IsFractionRing.idem F
  obtain ⟨g, hg⟩ := h
  obtain ⟨α, hα, rfl, b, U, hU, hG⟩ := exists_gram_of_isModular Q hL hLfg
  obtain ⟨b'⟩ := exists_basis (R := R) (F := F) hKfg
  obtain ⟨-, U', hU', hG'⟩ := (isModular_iff_gram Q' b' hα).mp hK
  obtain ⟨e, he⟩ := exists_basis_span (F := F) b
  obtain ⟨e', he'⟩ := exists_basis_span (F := F) b'
  -- two `F`-bases of `FK`: `g ∘ e` (reindexed) and `e'`
  let e₁ : Basis (Fin (finrank R K)) F (span F (K : Set V')) := (e.map g).reindex (finCongr hrk)
  obtain ⟨c, hc, hdet⟩ := exists_unit_det_gram (R := F) Q' e₁ e'
  have hge : (gram Q' fun i => (e₁ i : V')) = (gram Q fun i => (b i : V)).submatrix (finCongr hrk).symm
      (finCongr hrk).symm := by
    ext i j
    simp only [gram, Matrix.of_apply, Matrix.submatrix_apply, e₁, Basis.reindex_apply, Basis.map_apply]
    rw [← he, ← he]
    exact bil_eq_of_isometricLat (R := F) Q Q' g hg _ _
  have he'g : (gram Q' fun i => (e' i : V')) = gram Q' fun i => (b' i : V') := by
    ext i j; simp [gram, he']
  have hp : α ^ finrank R K = α ^ finrank R L := by rw [hrk]
  rw [hge, Matrix.det_submatrix_equiv_self, he'g, hG, hG', Matrix.det_smul, Matrix.det_smul,
    show (U.map (algebraMap R F)).det = algebraMap R F U.det from (RingHom.map_det _ _).symm,
    show (U'.map (algebraMap R F)).det = algebraMap R F U'.det from (RingHom.map_det _ _).symm,
    Fintype.card_fin, Fintype.card_fin, hp] at hdet
  -- `c² = det U' / det U` is a unit of `R`, so `c` is a unit of `R`
  have hαr : α ^ finrank R L ≠ 0 := pow_ne_zero _ hα
  have hcsq : c ^ 2 * algebraMap R F U.det = algebraMap R F U'.det := by
    have := hdet
    rw [show algebraMap F F c = c from rfl] at this
    apply mul_left_cancel₀ hαr
    linear_combination -this
  have hdu : IsUnit (U'.det * ↑hU.unit⁻¹) := hU'.mul (Units.isUnit _)
  obtain ⟨r, hr, hcr⟩ := exists_unit_of_sq_eq (R := R) (c := c) hdu (by
    rw [map_mul, ← hcsq]
    have : algebraMap R F (↑hU.unit⁻¹ : R) * algebraMap R F U.det = 1 := by
      rw [← map_mul, IsUnit.val_inv_mul, map_one]
    linear_combination (c ^ 2) * this.symm)
  refine ⟨b, b', ↑hr.unit⁻¹, Units.isUnit _, ?_⟩
  rw [hG, hG', Matrix.det_smul, Matrix.det_smul,
    show (U.map (algebraMap R F)).det = algebraMap R F U.det from (RingHom.map_det _ _).symm,
    show (U'.map (algebraMap R F)).det = algebraMap R F U'.det from (RingHom.map_det _ _).symm,
    Fintype.card_fin, Fintype.card_fin, hp, ← hcsq, hcr]
  have : algebraMap R F (↑hr.unit⁻¹ : R) * algebraMap R F r = 1 := by
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  linear_combination (-(α ^ finrank R L) * algebraMap R F U.det *
    (algebraMap R F (↑hr.unit⁻¹ : R) * algebraMap R F r + 1)) * this

end DVR

section LocalNonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Corollary 92:2a** (O'Meara 1963, p. 248): let $L$ and $K$ be lattices of the same Jordan type on a quadratic space
$V$ over a non-dyadic local field, with Jordan splittings $L = L_1 \perp \cdots \perp L_t$ and
$K = K_1 \perp \cdots \perp K_t$. Then $\operatorname{cls} L = \operatorname{cls} K$ if and only if $FL_i \cong FK_i$ for
$1 \le i \le t$. -/
@[kb "omeara1963" "§92, 92:2a, p. 248"]
theorem cls_eq_iff_isometric_span (h2 : IsUnit (2 : R)) {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F]
    {t t' : ℕ} {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (htype : SameJordanType Q Q Ls Ks) :
    cls Q L = cls Q K ↔ ∀ (i : Fin t) (j : Fin t'), (i : ℕ) = j →
      IsometricLat (R := F) Q Q (span F (Ls i : Set V)) (span F (Ks j : Set V)) := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  rw [cls_eq_iff_sameDisc Q h2 hL hK htype]
  obtain ⟨htt, hty⟩ := htype
  have key : ∀ (i : Fin t) (j : Fin t'), (i : ℕ) = j → (SameDisc Q Q (Ls i) (Ks j) ↔
      IsometricLat (R := F) Q Q (span F (Ls i : Set V)) (span F (Ks j : Set V))) := by
    intro i j hij
    have hj : j = Fin.cast htt i := Fin.ext (by simp [hij])
    subst hj
    obtain ⟨hsc, hrk, -⟩ := hty i
    have hfgi : (Ls i).FG := FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls i)
    have hfgj : (Ks (Fin.cast htt i)).FG := FG.of_le hKfg (hK.split.iSup_eq ▸ le_iSup Ks _)
    have hmodK : IsModular Q (scale Q (Ls i)) (Ks (Fin.cast htt i)) := by rw [hsc]; exact hK.modular _
    constructor
    · intro hd
      exact ((isometricLat_iff_sameDisc_of_isModular Q Q h2 hfgi hfgj (hL.modular i) hmodK hrk).mpr hd).span
        Q Q hfgi
    · exact sameDisc_of_isometric_span Q Q hfgi hfgj (hL.modular i) hmodK hrk
  exact forall₃_congr key

end LocalNonDyadic

end QuadFormsKB.OMeara
