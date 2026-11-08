/-
# Cassels, Chapter 11, proof of Lemma 9.2: case (a), the primes of $P$ where $f$ is isotropic

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Lemma 9.2, case (a), p. 246:
"$p \in P$, $k(p) = 0$. In this case $\mathbf u$ is close to $\pi^l\mathbf t$ … We take for $\Gamma_p$ the 3-dimensional lattice
$\Gamma_p = \sigma\Delta_p$. Then $\mathbf u$, $\Gamma_p$ have all the properties stated in Lemma 9.3 and its Corollary for
$\mathbf t$, $\Delta_p$", and the final stage (p. 249: "$p \in P^*$ … In case (a) this follows from Lemma 9.3").

**Proves.** `pkgCaseA`: if $\mathbf u$ (over $\mathbb Z_p$) has the shape of Lemma 9.3 with a lattice $\Delta = B'\mathbb Z_p^3$
(`Shape93`, obtained from Cassels' $\mathbf t$ by `Shape93.perturb`), then $\Gamma_p = \Delta$ (in the coordinates $W$) is a local
package (`LocalPkg`) for the integers $a$ with $p^{\mu+1} \mid a$ (i.e. $|a|_p < |f(\mathbf u)|_p$): every $b$ prime to $p$ works.
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma92Transport

open NumberField IsDedekindDomain Matrix QuadFormsKB.Cassels.Ch11L93

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

open QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-! ### Base change of the Gram form -/

theorem eval_map_hom {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} (Q : QuadForm R m)
    (x : Fin m → R) : (Q.map φ).eval (fun i => φ (x i)) = φ (Q.eval x) := by
  simp [QuadForm.evalIn, QuadForm.map, map_sum, apply_ite]

theorem col_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (B : Matrix (Fin 4) (Fin 3) R) (j : Fin 3) :
    Ch11L92.col (B.map φ) j = fun i => φ (Ch11L92.col B j i) := by
  funext i
  simp only [Ch11L92.col, mulVec_single_one, Matrix.col_apply, Matrix.map_apply]

/-- **The Gram form commutes with base change:** $(h \circ B)^\varphi = h^\varphi \circ B^\varphi$. -/
theorem gramOf_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (Q : QuadForm R 4)
    (B : Matrix (Fin 4) (Fin 3) R) : (gramOf Q B).map φ = gramOf (Q.map φ) (B.map φ) := by
  ext i j
  show φ ((gramOf Q B).coeff i j) = (gramOf (Q.map φ) (B.map φ)).coeff i j
  by_cases hij : i ≤ j
  · rw [gramOf_coeff _ _ i j hij, gramOf_coeff _ _ i j hij]
    split_ifs
    · rw [col_map, eval_map_hom]
    · rw [col_map, col_map, bl_map]
  · rw [(gramOf Q B).upper (lt_of_not_ge hij), (gramOf _ _).upper (lt_of_not_ge hij), map_zero]

/-! ### Case (a) -/

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- Helper: an integer vector whose image in $\mathbb Z_p^m$ has a unit coordinate is primitive at $p$. -/
theorem primAt_of_isUnit_cast {m : ℕ} (x : Fin m → ℤ) (h : ∃ i, IsUnit ((x i : ℤ) : ℤ_[pOf v])) :
    PrimAt (pOf v) x := by
  obtain ⟨i, hi⟩ := h
  intro hall
  obtain ⟨y, hy⟩ := hall i
  have : ((x i : ℤ) : ℤ_[pOf v]) = (pOf v : ℤ_[pOf v]) * (y : ℤ_[pOf v]) := by rw [hy]; push_cast; ring
  rw [this] at hi
  exact PadicInt.p_nonunit (isUnit_of_mul_isUnit_left hi)

theorem cast_mulVec {k m : ℕ} (M : Matrix (Fin k) (Fin m) ℤ) (x : Fin m → ℤ) (i : Fin k) :
    (((M *ᵥ x) i : ℤ) : ℤ_[pOf v]) = (M.map (Int.castRingHom ℤ_[pOf v]) *ᵥ fun j => ((x j : ℤ) : ℤ_[pOf v])) i := by
  simp [mulVec, dotProduct]

theorem hessian_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} (Q : QuadForm R m) :
    (Q.map φ).hessian = Q.hessian.map φ := by
  ext i j; simp [QuadForm.hessian, QuadForm.map]

/-- **Case (a) as a local package** (Cassels, p. 246 and p. 249). Data: the vector `u`, coordinates `W` with left
inverse `Wt` and $W\tilde W + c_0r^{\mathsf T} = 1$, $H_f\mathbf u = e\,r$ ($e \ne 0$), and a lattice $\Delta = B'\mathbb Z_p^3$ normal
to $\mathbf u$ with `Shape93` for $\mathbf u$ (over $\mathbb Z_p$, $p$ the prime of `v`). Then `Γ_p = \tilde W B'\mathbb Z_p^3` is a
local package for every set `A` of integers divisible by $p^{\mu+1}$, with modulus $p$ and $b_0 = 1$. -/
def pkgCaseA (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ) (Wt : Matrix (Fin 3) (Fin 4) ℤ)
    (c0 r : Fin 4 → ℤ) (hWW : W * Wt + Matrix.vecMulVec c0 r = 1) (e : ℤ) (he0 : e ≠ 0)
    (he : f.hessian *ᵥ u = e • r) (horth : ∀ z, bl f u (W *ᵥ z) = 0)
    (B' : Matrix (Fin 4) (Fin 3) ℤ_[pOf v]) (μ : ℕ) (u1 u2 : ℤ_[pOf v])
    (S : Shape93 (f.map (Int.castRingHom ℤ_[pOf v])) (fun i => (u i : ℤ_[pOf v])) B' μ u1 u2)
    (A : ℤ → Prop) (hA : ∀ a, A a → (pOf v : ℤ) ^ (μ + 1) ∣ a) (p0 : ℕ) : LocalPkg f u W A p0 v := by
  classical
  set φ := Int.castRingHom ℤ_[pOf v] with hφ
  set Qp := f.map φ with hQp
  set up : Fin 4 → ℤ_[pOf v] := fun i => (u i : ℤ_[pOf v]) with hup
  set C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v] := Wt.map φ * B' with hCdef
  -- the columns of `B'` are normal to `r`
  have hr0 : ∀ j, (fun i => (r i : ℤ_[pOf v])) ⬝ᵥ Ch11L92.col B' j = 0 := by
    intro j
    have h1 := S.orth j
    rw [bl_comm, bl, hessian_map] at h1
    have h2 : Qp.hessian *ᵥ up = (e : ℤ_[pOf v]) • fun i => (r i : ℤ_[pOf v]) := by
      rw [hQp, hessian_map]
      funext i
      have := congrFun he i
      simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [hup, hφ, ← cast_mulVec, this]; simp
    rw [← hessian_map] at h1
    rw [h2, dotProduct_smul, smul_eq_mul, dotProduct_comm] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (by exact_mod_cast h) he0
    · exact h
  -- `W C = B'`
  have hWC : W.map φ * C = B' := by
    have hm : W.map φ * Wt.map φ = 1 - Matrix.vecMulVec (fun i => (c0 i : ℤ_[pOf v])) (fun i => (r i : ℤ_[pOf v])) := by
      rw [← Matrix.map_mul, eq_sub_iff_add_eq]
      have := congrArg (fun M => M.map φ) hWW
      simp only [Matrix.map_add, Matrix.map_one _ (map_zero φ) (map_one φ)] at this
      rw [← this]; congr 1; ext i j; simp [Matrix.vecMulVec_apply, φ]
    rw [hCdef, ← Matrix.mul_assoc, hm, Matrix.sub_mul, Matrix.one_mul, sub_eq_self]
    refine Matrix.ext fun i j => ?_
    have := hr0 j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    simp only [Ch11L92.col, mulVec_single_one, Matrix.col_apply, dotProduct] at this
    rw [show ∑ k, (c0 i : ℤ_[pOf v]) * (r k : ℤ_[pOf v]) * B' k j = (c0 i : ℤ_[pOf v]) * ∑ k, (r k : ℤ_[pOf v]) * B' k j
      by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, this, mul_zero]
  have hWCv : ∀ η, W.map φ *ᵥ (C *ᵥ η) = B' *ᵥ η := fun η => by rw [mulVec_mulVec, hWC]
  -- `det C ≠ 0`
  have hC : C.det ≠ 0 := by
    intro h0
    obtain ⟨η, hη0, hη⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hη0
    have hB : B' *ᵥ η = 0 := by rw [← hWCv, hη, mulVec_zero]
    have hlin := Fintype.linearIndependent_iff.mp S.indep (fun j => (η j : ℚ_[pOf v])) (by
      funext i
      have := congrFun hB i
      simp only [mulVec, dotProduct, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have := congrArg (fun x : ℤ_[pOf v] => (x : ℚ_[pOf v])) this
      simp only [PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_zero] at this
      rw [← this]; exact Finset.sum_congr rfl fun j _ => by ring)
    funext j; exact Subtype.ext (hlin j)
  -- evaluation of `h` on `C η`
  have hev : ∀ η, ((gramOf f W).map φ).eval (C *ᵥ η) = Qp.eval (B' *ᵥ η) := by
    intro η; rw [gramOf_map, gramOf_eval, hWCv]
  -- polar values on `Δ`
  have hq : ∀ i, (pOf v : ℤ_[pOf v]) ^ μ ∣ bl Qp (Ch11L92.col B' i) (Ch11L92.col B' i) := by
    intro i
    rw [bl_self]
    refine Dvd.dvd.mul_left ?_ _
    fin_cases i
    · exact (pow_dvd_pow _ (Nat.le_succ μ)).trans S.q0
    · exact (pow_dvd_pow _ (Nat.le_succ μ)).trans S.q1
    · exact S.q2
  have h01 : (pOf v : ℤ_[pOf v]) ^ μ ∣ bl Qp (Ch11L92.col B' 0) (Ch11L92.col B' 1) := by
    have h := dvd_add ((pow_dvd_pow _ (Nat.le_succ μ)).trans S.b01) (dvd_mul_right ((pOf v : ℤ_[pOf v]) ^ μ) u1)
    simpa using h
  have h10 : (pOf v : ℤ_[pOf v]) ^ μ ∣ bl Qp (Ch11L92.col B' 1) (Ch11L92.col B' 0) := by rw [bl_comm]; exact h01
  have h20 : (pOf v : ℤ_[pOf v]) ^ μ ∣ bl Qp (Ch11L92.col B' 2) (Ch11L92.col B' 0) := by rw [bl_comm]; exact S.b02
  have h21 : (pOf v : ℤ_[pOf v]) ^ μ ∣ bl Qp (Ch11L92.col B' 2) (Ch11L92.col B' 1) := by rw [bl_comm]; exact S.b12
  have hrow : ∀ (i : Fin 3) (η' : Fin 3 → ℤ_[pOf v]), (pOf v : ℤ_[pOf v]) ^ μ ∣ bl Qp (Ch11L92.col B' i) (B' *ᵥ η') := by
    intro i η'
    rw [bl_mulVec_three]
    fin_cases i
    · exact dvd_add (dvd_add (Dvd.dvd.mul_left (hq 0) _) (Dvd.dvd.mul_left h01 _)) (Dvd.dvd.mul_left S.b02 _)
    · exact dvd_add (dvd_add (Dvd.dvd.mul_left h10 _) (Dvd.dvd.mul_left (hq 1) _)) (Dvd.dvd.mul_left S.b12 _)
    · exact dvd_add (dvd_add (Dvd.dvd.mul_left h20 _) (Dvd.dvd.mul_left h21 _)) (Dvd.dvd.mul_left (hq 2) _)
  have hbilB : ∀ η η' : Fin 3 → ℤ_[pOf v], (pOf v : ℤ_[pOf v]) ^ μ ∣ bl Qp (B' *ᵥ η) (B' *ᵥ η') := by
    intro η η'
    rw [bl_comm, bl_mulVec_three]
    refine dvd_add (dvd_add ?_ ?_) ?_ <;> refine Dvd.dvd.mul_left ?_ _ <;> rw [bl_comm] <;> exact hrow _ η'
  refine
    { M := tLat v hC
      isLattice := tLat_isLattice v hC
      le_std := tLat_le_std v hC
      units := fun L hQ hL w hw => units_mem_tLat v (gramOf f W) hC μ (fun η η' => ?_) (fun w' hw' => ?_) L hQ hL w hw
      N := 1
      cond := fun a ha => ⟨1, fun b hb => ?_⟩ }
  · rw [← mulVec_add, hev, hev, hev, mulVec_add, eval_add]
    convert hbilB η η' using 1; ring
  · obtain ⟨x0, hx0⟩ := S.q0
    obtain ⟨x1, hx1⟩ := S.q1
    obtain ⟨x01, hx01⟩ := S.b01
    obtain ⟨a, ha⟩ := exists_root_quadratic ((pOf v : ℤ_[pOf v]) * x1 - w') (u1 + (pOf v : ℤ_[pOf v]) * x01) x0
      (isUnit_add_p_mul S.hu1 x01)
    refine ⟨![a, 1, 0], ?_⟩
    rw [hev, eval_mulVec_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have e01 : bl Qp (Ch11L92.col B' 0) (Ch11L92.col B' 1) =
        (pOf v : ℤ_[pOf v]) ^ μ * u1 + (pOf v : ℤ_[pOf v]) ^ (μ + 1) * x01 := by linear_combination hx01
    rw [hx0, hx1, e01]
    linear_combination (pOf v : ℤ_[pOf v]) ^ μ * ha
  · -- the local conditions on `b`
    have hpb : ¬ (pOf v : ℤ) ∣ b := by
      intro hd
      have h1 : ((pOf v ^ 1 : ℕ) : ℤ) ∣ b - 1 := (Int.ModEq.dvd hb.symm)
      have : (pOf v : ℤ) ∣ 1 := by
        have := dvd_sub hd (by simpa using h1); simpa using this
      exact (Fact.out : (pOf v).Prime).one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
    have hbu : IsUnit (b : ℤ_[pOf v]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hpb ?_)
      exact (PadicInt.norm_int_lt_one_iff_dvd b).mp hlt
    obtain ⟨bi, hbi⟩ := hbu.exists_right_inv
    have hap : (pOf v : ℤ_[pOf v]) ^ (μ + 1) ∣ (a : ℤ_[pOf v]) := by
      obtain ⟨t, ht⟩ := hA a ha; exact ⟨t, by rw [ht]; push_cast; ring⟩
    have hQu : Qp.eval up = (f.eval u : ℤ_[pOf v]) := by
      exact eval_map_hom φ f u
    refine ⟨?_, fun z hzM hz => Or.inl ?_⟩
    · -- representation (Corollary to Lemma 9.3)
      obtain ⟨Y, hY⟩ := S.cor ((a : ℤ_[pOf v]) * bi ^ 2) (Dvd.dvd.mul_right ((pow_dvd_pow _ (Nat.le_succ μ)).trans hap) _)
      rw [S.eval_t_add] at hY
      refine exists_mem_tLat_of_rep v (gramOf f W) hC ⟨(b : ℤ_[pOf v]) • Y, ?_⟩
      rw [hev, mulVec_smul, eval_smul]
      rw [hQu] at hY
      push_cast
      linear_combination (b : ℤ_[pOf v]) ^ 2 * hY + ((a : ℤ_[pOf v]) * ((b : ℤ_[pOf v]) * bi + 1)) * hbi
    · -- primitivity (Lemma 9.3 (ii))
      obtain ⟨η, hη⟩ := (intVec_mem_tLat_iff v hC z).mp hzM
      have hfa : f.eval (b • u + W *ᵥ z) = a := by
        rw [eval_split f u W horth, hz]; ring
      have hcast : (fun i => (((b • u + W *ᵥ z) i : ℤ) : ℤ_[pOf v])) = (b : ℤ_[pOf v]) • up + B' *ᵥ η := by
        rw [← hWCv, ← hη]
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hup]
        rw [Int.cast_add, Int.cast_mul, hφ, cast_mulVec]
      have hval : Qp.eval ((b : ℤ_[pOf v]) • up + B' *ᵥ η) = (a : ℤ_[pOf v]) := by
        have := eval_map_hom φ f (b • u + W *ᵥ z)
        rw [hfa] at this
        rw [← hcast]; exact this
      have hdiv : (pOf v : ℤ_[pOf v]) ^ (μ + 1) ∣ Qp.eval (up + B' *ᵥ (bi • η)) := by
        have e : (b : ℤ_[pOf v]) • (up + B' *ᵥ (bi • η)) = (b : ℤ_[pOf v]) • up + B' *ᵥ η := by
          rw [smul_add, mulVec_smul, smul_smul, hbi, one_smul]
        have : Qp.eval (up + B' *ᵥ (bi • η)) = bi ^ 2 * (a : ℤ_[pOf v]) := by
          have h1 : (b : ℤ_[pOf v]) ^ 2 * Qp.eval (up + B' *ᵥ (bi • η)) = (a : ℤ_[pOf v]) := by
            rw [← hval, ← e, eval_smul]
          linear_combination bi ^ 2 * h1 - (Qp.eval (up + B' *ᵥ (bi • η)) * (1 + (b : ℤ_[pOf v]) * bi)) * hbi
        rw [this]; exact Dvd.dvd.mul_left hap _
      obtain ⟨i, hi⟩ := S.prim' (bi • η) hdiv
      apply primAt_of_isUnit_cast v
      refine ⟨i, ?_⟩
      have := congrFun hcast i
      rw [this]
      have e : ((b : ℤ_[pOf v]) • up + B' *ᵥ η) i = (b : ℤ_[pOf v]) * (up + B' *ᵥ (bi • η)) i := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_smul]
        rw [mul_add, ← mul_assoc, hbi, one_mul]
      rw [e]; exact hbu.mul hi

end QuadFormsKB.Cassels.Ch11L92
