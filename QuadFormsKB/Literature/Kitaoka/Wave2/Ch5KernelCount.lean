/-
# Kitaoka 1993, §5.6: the kernel of a $p$-adic matrix on residues modulo $p^t$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, proof of Theorem 5.6.4 (b), p. 116:
"$\#\{\varphi : M \to (p^tN' \cap N)/p^tN\} = [p^tN' \cap N : p^tN]^m \le [N' : N]^m$".

**Setting.** $p$ is a prime, $C \in M_n(\mathbb Z_p)$ with $\det C \neq 0$ (the matrix of an inclusion $N \subseteq N'$
of lattices of full rank), $t \ge 0$.  Residues modulo $p^t$ are the numbers $0 \le a < p^t$ (elements of
`Fin (p ^ t)`), viewed in $\mathbb Z_p$ through the natural cast.

**Proves**
* `card_quot_span` : for $a \ne 0$, $\#(\mathbb Z_p / a\mathbb Z_p) = \lVert a\rVert_p^{-1}$;
* `card_quot_range` : for $\det C \ne 0$, the quotient $\mathbb Z_p^n / C\mathbb Z_p^n$ is finite of cardinality
  $\lVert\det C\rVert_p^{-1}$ (Smith normal form over the principal ideal domain $\mathbb Z_p$);
* `card_ker_le` : the number of $y \in \{0,\dots,p^t-1\}^n$ with $C y \equiv 0 \bmod p^t$ is at most
  $\lVert\det C\rVert_p^{-1} = [\mathbb Z_p^n : C\mathbb Z_p^n]$;
* `card_ker_mat_le` : the same for $n \times m$ matrices $Y$ (columns independent), the bound being
  $\lVert\det C\rVert_p^{-m}$.

*Proof sketch.* Choose $z(y) \in \mathbb Z_p^n$ with $Cy = p^t z(y)$ and send $y$ to the class of $z(y)$ in
$\mathbb Z_p^n / C\mathbb Z_p^n$.  If $z(y)-z(y') = Cw$ then $C(y - y') = C(p^tw)$, so $y - y' = p^tw$ because $C$ is
injective, hence $y \equiv y' \bmod p^t$ and $y = y'$ as both are reduced residues.  So this map is injective, and
the cardinality of its target is $\lVert\det C\rVert_p^{-1}$: by the Smith normal form the quotient is
$\prod_i \mathbb Z_p/a_i\mathbb Z_p$ with $\det C$ associated to $\prod_i a_i$, and
$\mathbb Z_p / p^k\mathbb Z_p \cong \mathbb Z/p^k\mathbb Z$ has $p^k = \lVert p^k\rVert_p^{-1}$ elements.
-/
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Determinant

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- $\mathbb Z_p / p^k\mathbb Z_p \cong \mathbb Z / p^k\mathbb Z$. -/
def quot_pow_equiv (k : ℕ) : (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ k}) ≃+* ZMod (p ^ k) :=
  (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow (p := p) k)).symm.trans
    (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) k)))

/-- $\mathbb Z_p / p^k\mathbb Z_p$ is finite. -/
theorem finite_quot_pow (k : ℕ) : Finite (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ k}) := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact Finite.of_equiv (ZMod (p ^ k)) (quot_pow_equiv k).toEquiv.symm

/-- $\#(\mathbb Z_p / p^k\mathbb Z_p) = p^k$. -/
theorem card_quot_pow (k : ℕ) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ k}) = p ^ k := by
  rw [Nat.card_congr (quot_pow_equiv k).toEquiv, Nat.card_zmod]

/-- For $a \neq 0$ the quotient $\mathbb Z_p / a\mathbb Z_p$ is finite and has $\lVert a\rVert_p^{-1}$ elements. -/
theorem card_quot_span (a : ℤ_[p]) (ha : a ≠ 0) :
    Finite (ℤ_[p] ⧸ Ideal.span {a}) ∧
      (Nat.card (ℤ_[p] ⧸ Ideal.span {a}) : ℝ) = ‖a‖⁻¹ := by
  have h := PadicInt.unitCoeff_spec ha
  have hs : Ideal.span {a} = Ideal.span {(p : ℤ_[p]) ^ a.valuation} := by
    conv_lhs => rw [h]
    exact Ideal.span_singleton_mul_left_unit (Units.isUnit _) _
  have hn : ‖a‖ = (p : ℝ) ^ (-(a.valuation : ℤ)) := by
    calc ‖a‖ = ‖((PadicInt.unitCoeff ha : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ a.valuation‖ :=
          congrArg _ h
      _ = _ := by
        rw [norm_mul, PadicInt.isUnit_iff.mp (Units.isUnit _), one_mul, PadicInt.norm_p_pow]
  refine ⟨?_, ?_⟩
  · rw [hs]; exact finite_quot_pow _
  · rw [hs, card_quot_pow, hn, zpow_neg, zpow_natCast, inv_inv]
    push_cast; rfl

/-- If `C` has nonzero determinant then `C.mulVecLin` is injective. -/
theorem mulVecLin_injective_of_det_ne_zero (C : Matrix (Fin n) (Fin n) ℤ_[p]) (hC : C.det ≠ 0) :
    Function.Injective C.mulVecLin := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  exact hC (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hne, hv⟩)

/-- For `C` with nonzero determinant, the quotient $\mathbb Z_p^n / C\mathbb Z_p^n$ is finite and has
$\lVert\det C\rVert_p^{-1}$ elements (Smith normal form over the principal ideal domain $\mathbb Z_p$). -/
theorem card_quot_range (C : Matrix (Fin n) (Fin n) ℤ_[p]) (hC : C.det ≠ 0) :
    Finite ((Fin n → ℤ_[p]) ⧸ LinearMap.range C.mulVecLin) ∧
      (Nat.card ((Fin n → ℤ_[p]) ⧸ LinearMap.range C.mulVecLin) : ℝ) = ‖C.det‖⁻¹ := by
  have hinj := mulVecLin_injective_of_det_ne_zero C hC
  set N : Submodule ℤ_[p] (Fin n → ℤ_[p]) := LinearMap.range C.mulVecLin with hN
  let e0 : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] N := LinearEquiv.ofInjective C.mulVecLin hinj
  have h : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] (Fin n → ℤ_[p]) :=
    e0.symm.finrank_eq
  let b := Pi.basisFun ℤ_[p] (Fin n)
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] N := b'.equiv ab (Equiv.refl _)
  let f : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ℤ_[p]) := N.subtype.comp (e' : _ →ₗ[ℤ_[p]] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    show ((b'.equiv ab (Equiv.refl _)) (b' i) : Fin n → ℤ_[p]) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    calc LinearMap.det f = (LinearMap.toMatrix b' b' f).det := by rw [LinearMap.det_toMatrix]
      _ = (Matrix.diagonal a).det := ?_
      _ = ∏ i, a i := by rw [Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hassoc : Associated C.det (∏ i, a i) := by
    have h1 : LinearMap.det (N.subtype.comp (e0 : _ →ₗ[ℤ_[p]] N)) = C.det := by
      have : N.subtype.comp (e0 : _ →ₗ[ℤ_[p]] N) = Matrix.toLin' C := by
        exact LinearMap.ext fun x => by simp [e0, N]
      rw [this, LinearMap.det_toLin']
    rw [← h1, ← hdetf]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have hnorm : ‖C.det‖ = ∏ i, ‖a i‖ := by
    obtain ⟨u, hu⟩ := hassoc
    rw [← norm_prod, ← hu, norm_mul, PadicInt.isUnit_iff.mp (Units.isUnit _), mul_one]
  have hq := Submodule.quotientEquivPiSpan N b h
  have hai : ∀ i, Finite (ℤ_[p] ⧸ Ideal.span {a i}) ∧
      (Nat.card (ℤ_[p] ⧸ Ideal.span {a i}) : ℝ) = ‖a i‖⁻¹ :=
    fun i => card_quot_span _ (Submodule.smithNormalFormCoeffs_ne_zero b h i)
  have : ∀ i, Finite (ℤ_[p] ⧸ Ideal.span {a i}) := fun i => (hai i).1
  refine ⟨Finite.of_equiv _ hq.toEquiv.symm, ?_⟩
  rw [Nat.card_congr hq.toEquiv, Nat.card_pi, hnorm]
  push_cast
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => (hai i).2

/-- A natural number $y < p^t$ that is divisible by $p^t$ in $\mathbb Z_p$ is zero; more precisely two such
residues congruent in $\mathbb Z_p$ modulo $p^t$ are equal. -/
theorem fin_eq_of_dvd (t : ℕ) (a b : Fin (p ^ t))
    (h : (p : ℤ_[p]) ^ t ∣ (((a : ℕ) : ℤ_[p]) - ((b : ℕ) : ℤ_[p]))) : a = b := by
  have h1 : (PadicInt.toZModPow t) (((a : ℕ) : ℤ_[p]) - ((b : ℕ) : ℤ_[p])) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact h
  rw [map_sub, map_natCast, map_natCast, sub_eq_zero,
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at h1
  exact Fin.ext h1

/-- **Kernel count** (Kitaoka, proof of Thm 5.6.4 (b)).  For $C \in M_n(\mathbb Z_p)$ with $\det C \ne 0$, the
number of residue vectors $y \in \{0,\dots,p^t-1\}^n$ with $Cy \equiv 0 \bmod p^t$ is at most
$\lVert\det C\rVert_p^{-1} = [\mathbb Z_p^n : C\mathbb Z_p^n]$. -/
theorem card_ker_le (C : Matrix (Fin n) (Fin n) ℤ_[p]) (hC : C.det ≠ 0) (t : ℕ) :
    (Nat.card {y : Fin n → Fin (p ^ t) //
        ∀ i, (p : ℤ_[p]) ^ t ∣ (C *ᵥ fun j => (((y j : ℕ)) : ℤ_[p])) i} : ℝ) ≤ ‖C.det‖⁻¹ := by
  obtain ⟨hfin, hcard⟩ := card_quot_range C hC
  have hinj := mulVecLin_injective_of_det_ne_zero C hC
  set N : Submodule ℤ_[p] (Fin n → ℤ_[p]) := LinearMap.range C.mulVecLin with hN
  have hex : ∀ y : {y : Fin n → Fin (p ^ t) //
        ∀ i, (p : ℤ_[p]) ^ t ∣ (C *ᵥ fun j => (((y j : ℕ)) : ℤ_[p])) i},
      ∃ z : Fin n → ℤ_[p], (C *ᵥ fun j => (((y.1 j : ℕ)) : ℤ_[p])) = (p : ℤ_[p]) ^ t • z := by
    intro y
    choose z hz using y.2
    exact ⟨z, funext fun i => by simpa using hz i⟩
  choose z hz using hex
  let F : {y : Fin n → Fin (p ^ t) //
        ∀ i, (p : ℤ_[p]) ^ t ∣ (C *ᵥ fun j => (((y j : ℕ)) : ℤ_[p])) i} →
      ((Fin n → ℤ_[p]) ⧸ N) := fun y => Submodule.Quotient.mk (z y)
  have hF : Function.Injective F := by
    intro y y' hyy
    have hmem : z y - z y' ∈ N := (Submodule.Quotient.eq N).1 hyy
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hmem
    have key : C *ᵥ ((fun j => (((y.1 j : ℕ)) : ℤ_[p])) - fun j => (((y'.1 j : ℕ)) : ℤ_[p]))
        = C *ᵥ ((p : ℤ_[p]) ^ t • w) := by
      rw [Matrix.mulVec_sub, hz y, hz y', Matrix.mulVec_smul, ← smul_sub]
      congr 1
      exact hw.symm
    have key2 := hinj key
    apply Subtype.ext
    funext j
    apply fin_eq_of_dvd
    have := congrFun key2 j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    exact ⟨w j, this⟩
  have := hfin
  have := Nat.card_le_card_of_injective F hF
  rw [← hcard]
  exact_mod_cast this

/-- **Kernel count, $m$ columns** (Kitaoka, proof of Thm 5.6.4 (b)).  For $C \in M_n(\mathbb Z_p)$ with
$\det C \ne 0$, the number of residue matrices $Y \in M_{n \times m}(\{0,\dots,p^t-1\})$ with
$CY \equiv 0 \bmod p^t$ is at most $\lVert\det C\rVert_p^{-m}$. -/
theorem card_ker_mat_le (C : Matrix (Fin n) (Fin n) ℤ_[p]) (hC : C.det ≠ 0) (t m : ℕ) :
    (Nat.card {Y : Matrix (Fin n) (Fin m) (Fin (p ^ t)) //
        ∀ i j, (p : ℤ_[p]) ^ t ∣ (C * Y.map fun a => (((a : ℕ)) : ℤ_[p])) i j} : ℝ) ≤
      ‖C.det‖⁻¹ ^ m := by
  let S := {y : Fin n → Fin (p ^ t) //
        ∀ i, (p : ℤ_[p]) ^ t ∣ (C *ᵥ fun j => (((y j : ℕ)) : ℤ_[p])) i}
  have hmul : ∀ (Y : Matrix (Fin n) (Fin m) (Fin (p ^ t))) i j,
      (C * Y.map fun a => (((a : ℕ)) : ℤ_[p])) i j =
        (C *ᵥ fun k => (((Y k j : Fin (p ^ t)) : ℕ) : ℤ_[p])) i := by
    intro Y i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  let e : {Y : Matrix (Fin n) (Fin m) (Fin (p ^ t)) //
        ∀ i j, (p : ℤ_[p]) ^ t ∣ (C * Y.map fun a => (((a : ℕ)) : ℤ_[p])) i j} ≃
      (Fin m → S) :=
    { toFun := fun Y j => ⟨fun k => Y.1 k j, fun i => by
        rw [← hmul]; exact Y.2 i j⟩
      invFun := fun f => ⟨Matrix.of fun k j => (f j).1 k, fun i j => by
        rw [hmul]; exact (f j).2 i⟩
      left_inv := fun Y => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr e, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (card_ker_le C hC t) m

end QuadFormsKB.Kitaoka.Density

end
