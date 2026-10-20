/-
# Kneser neighbours at principal primes, any class number (without $h_F = 1$)

**Setting.** $F$ a number field (any class number), $Q$ a form over $\mathcal O_F$, $\pi$ a **prime element** (so $\mathfrak p = (\pi)$ is a
principal prime) with $\pi \nmid \det H$, $\vec v \in \mathcal O_F^n$ with $\pi^2 \mid Q(\vec v)$, $\bar{\vec v} \ne 0$, and the explicit neighbour
$L(\vec v) = L_{\vec v} + \mathcal O_F\frac1\pi\vec v$ (`Nbr.nbLat`).

**Main results.**
* **`exists_latOf_nbLat`**: $L(\vec v)$ is free, $L(\vec v) = \delta\mathcal O_F^n$. Before, this came from $\mathcal O_F$ being a PID. *Proof:* away
  from $\pi$, $L(\vec v)_\mathfrak q = \mathfrak o_\mathfrak q^n$ (`loc_nbLat_of_ne`); at $\pi$, the explicit vectors $\frac1\pi\vec v$, $\pi e_{j_0}$,
  $\beta_{j_0}e_c - \beta_ce_{j_0}$ ($\beta = H\vec v$, $\pi \nmid v_{i_0}\beta_{j_0}$, `exists_coords`) lie in $L(\vec v)$ (`nbMat_col_mem`), have
  determinant a unit at $\pi$ (`valuation_det_nbMat`), and span $L(\vec v)_\pi$ because their Gram matrix $G$ is unimodular at $\pi$:
  $G\,\gamma^{-1}x = (B(\gamma e_i, x))_i$ is integral (`valuation_inv_mulVec_le`). So the Steinitz class is trivial
  (`Steinitz.exists_latOf_of_loc`).
* **`sameGenus_glImage_nbLat'`**, **`nbrInGenus'`**: $\pi$-neighbours of lattices in the genus of $\mathcal O_F^n$ stay in the genus (Kneser 1957,
  Satz 1) for every prime element $\pi \nmid 2\det H$, with no class-number hypothesis (the PID versions are in `HeckeGenusLocal.lean`).

Sources: Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), Satz 1 [unverified]; O'Meara (1963), 82:15
(unimodular lattices are maximal) [unverified].
-/
import QuadFormsKB.HilbertModular.HeckeGenusLocal
import QuadFormsKB.Lattices.Steinitz

open Matrix NumberField IsDedekindDomain
open scoped Pointwise

set_option linter.unusedSectionVars false

attribute [local instance] Ideal.Quotient.field

noncomputable section

namespace QuadFormsKB.HilbertModular.NeighborsNP

open QuadFormsKB.Lattices QuadFormsKB.Lattices.Nbr QuadFormsKB.LocalDensity QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

variable {π : 𝓞 F} (hπ : Prime π) {Q : QuadForm (𝓞 F) n} (hdet : ¬ π ∣ Q.hessian.det)
  {v : Fin n → 𝓞 F} (hv : π ^ 2 ∣ Nbr.qv (𝓞 F) Q v) (hv0 : red π v ≠ 0)

/-- $B(x, v) = x \cdot (Hv)$ over $\mathcal O_F$. -/
lemma bv_eq_dot (x : Fin n → 𝓞 F) : Nbr.bv (𝓞 F) Q x v = x ⬝ᵥ (Q.hessian *ᵥ v) := by
  simp [Nbr.bv]

include hπ hdet hv hv0 in
/-- **Coordinates for the neighbour**: $\pi \nmid v_{i_0}$ and $\pi \nmid (Hv)_{j_0}$ for some $i_0 \ne j_0$. -/
lemma exists_coords : ∃ i₀ j₀ : Fin n, i₀ ≠ j₀ ∧ ¬ π ∣ v i₀ ∧ ¬ π ∣ (Q.hessian *ᵥ v) j₀ := by
  classical
  have := isMaximal_span hπ
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ¬ π ∣ v i₀ := by
    by_contra h
    push Not at h
    exact hv0 ((red_eq_zero_iff v).mpr h)
  refine ⟨i₀, ?_⟩
  by_contra hcon
  push Not at hcon
  -- all `(Hv)_j`, `j ≠ i₀`, are divisible by `π`
  have hβ : ∀ j, j ≠ i₀ → π ∣ (Q.hessian *ᵥ v) j := fun j hj => hcon j (Ne.symm hj) hi₀
  -- `B(v, v) = 2 Q(v) ≡ 0`, so also `(Hv)_{i₀}`
  have hvv : π ∣ v ⬝ᵥ (Q.hessian *ᵥ v) := by
    rw [← bv_eq_dot, Nbr.bv_self]
    exact dvd_mul_of_dvd_right ((dvd_pow_self π two_ne_zero).trans hv) 2
  have hβi : π ∣ (Q.hessian *ᵥ v) i₀ := by
    have h1 : v ⬝ᵥ (Q.hessian *ᵥ v) = v i₀ * (Q.hessian *ᵥ v) i₀ +
        ∑ j ∈ Finset.univ.erase i₀, v j * (Q.hessian *ᵥ v) j := by
      rw [dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have h2 : π ∣ ∑ j ∈ Finset.univ.erase i₀, v j * (Q.hessian *ᵥ v) j :=
      Finset.dvd_sum fun j hj => dvd_mul_of_dvd_right (hβ j (Finset.ne_of_mem_erase hj)) _
    have h3 : π ∣ v i₀ * (Q.hessian *ᵥ v) i₀ := by
      have := dvd_sub hvv h2
      rwa [h1, add_sub_cancel_right] at this
    exact (hπ.dvd_or_dvd h3).resolve_left hi₀
  have hall : ∀ j, π ∣ (Q.hessian *ᵥ v) j := fun j => by
    by_cases hj : j = i₀
    · subst hj; exact hβi
    · exact hβ j hj
  -- then `H̄ v̄ = 0` with `v̄ ≠ 0`, so `π ∣ det H`
  apply hdet
  rw [← dvd_of_red]
  have hmul : (Q.hessian.map (algebraMap (𝓞 F) (Res π))) *ᵥ red π v = 0 := by
    funext j
    have := (dvd_of_red (π := π) _).mpr (hall j)
    rw [Pi.zero_apply, ← this]
    exact (RingHom.map_mulVec (algebraMap (𝓞 F) (Res π)) Q.hessian v j).symm
  have h0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨red π v, hv0, hmul⟩
  rw [show (Q.hessian.map (algebraMap (𝓞 F) (Res π))).det = algebraMap (𝓞 F) (Res π) Q.hessian.det from
    (RingHom.map_det _ _).symm] at h0
  exact h0


variable (Q) (π) (v) in
/-- The explicit vectors of $L(\vec v)$: $\gamma = A\,D\,U$ with columns $\frac1\pi\vec v$ (at $i_0$), $\pi e_{j_0}$ (at $j_0$) and
$\beta_{j_0}e_c - \beta_ce_{j_0}$ ($\beta = H\vec v$) elsewhere. -/
def nbMat (i₀ j₀ : Fin n) : Matrix (Fin n) (Fin n) F :=
  ((1 : Matrix (Fin n) (Fin n) F).updateCol i₀ ((ιO π)⁻¹ • cv F v)) *
    Matrix.diagonal (fun c => if c = j₀ then ιO π else if c = i₀ then 1 else ιO ((Q.hessian *ᵥ v) j₀)) *
    (1 : Matrix (Fin n) (Fin n) F).updateRow j₀
      (fun c => if c = j₀ then 1 else if c = i₀ then 0 else -(ιO ((Q.hessian *ᵥ v) c) / ιO π))

lemma updateCol_one_mulVec_single {i₀ c : Fin n} (w : Fin n → F) :
    ((1 : Matrix (Fin n) (Fin n) F).updateCol i₀ w) *ᵥ Pi.single c 1 = if c = i₀ then w else Pi.single c 1 := by
  rw [Matrix.mulVec_single_one]
  ext r
  by_cases hc : c = i₀
  · subst hc; simp [Matrix.col]
  · simp [Matrix.col, Matrix.updateCol_apply, hc, Matrix.one_apply, Pi.single_apply, eq_comm]

lemma updateRow_one_mulVec_single {j₀ c : Fin n} (r : Fin n → F) :
    ((1 : Matrix (Fin n) (Fin n) F).updateRow j₀ r) *ᵥ Pi.single c 1 =
      Pi.single c 1 + (r c - if c = j₀ then 1 else 0) • Pi.single j₀ 1 := by
  rw [Matrix.mulVec_single_one]
  ext i
  by_cases hi : i = j₀
  · subst hi; by_cases hc : c = i <;> simp [Matrix.col, hc, Pi.single_apply]
  · simp [Matrix.col, Matrix.updateRow_apply, hi, Matrix.one_apply, Pi.single_apply, eq_comm]

include hπ in
lemma nbMat_col {i₀ j₀ : Fin n} (hij : i₀ ≠ j₀) (c : Fin n) :
    nbMat π Q v i₀ j₀ *ᵥ Pi.single c 1 =
      if c = i₀ then (ιO π)⁻¹ • cv F v else if c = j₀ then ιO π • Pi.single j₀ 1 else
        cv F ((Q.hessian *ᵥ v) j₀ • Pi.single c 1 - (Q.hessian *ᵥ v) c • Pi.single j₀ 1) := by
  classical
  have h0 := πK_ne_zero (K := F) hπ
  rw [nbMat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, updateRow_one_mulVec_single]
  set β := Q.hessian *ᵥ v
  set d : Fin n → F := fun c => if c = j₀ then ιO π else if c = i₀ then 1 else ιO (β j₀)
  set r : Fin n → F := fun c => if c = j₀ then 1 else if c = i₀ then 0 else -(ιO (β c) / ιO π)
  set A := (1 : Matrix (Fin n) (Fin n) F).updateCol i₀ ((ιO π)⁻¹ • cv F v)
  have hD : ∀ c, Matrix.diagonal d *ᵥ Pi.single c 1 = d c • Pi.single c 1 := fun c => by
    ext i; by_cases h : i = c
    · subst h; simp [Matrix.mulVec_diagonal]
    · simp [Matrix.mulVec_diagonal, h]
  have hA : ∀ c, c ≠ i₀ → A *ᵥ Pi.single c 1 = Pi.single c 1 := fun c hc => by
    rw [updateCol_one_mulVec_single, if_neg hc]
  have hAi : A *ᵥ Pi.single i₀ 1 = (ιO π)⁻¹ • cv F v := by rw [updateCol_one_mulVec_single, if_pos rfl]
  by_cases hci : c = i₀
  · subst hci
    have : r c - (if c = j₀ then 1 else 0) = 0 := by simp [r, hij]
    rw [this, zero_smul, add_zero, hD, Matrix.mulVec_smul, hAi, if_pos rfl]
    simp [d, hij]
  · by_cases hcj : c = j₀
    · subst hcj
      have : r c - (if c = c then 1 else 0) = 0 := by simp [r]
      rw [this, zero_smul, add_zero, hD, Matrix.mulVec_smul, hA c hci, if_neg hci, if_pos rfl]
      simp [d]
    · have : r c - (if c = j₀ then 1 else 0) = -(ιO (β c) / ιO π) := by simp [r, hcj, hci]
      rw [this]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hD, hA c hci, hA j₀ (Ne.symm hij), if_neg hci,
        if_neg hcj]
      ext i
      simp only [d, if_neg hcj, if_neg hci, if_pos rfl, cv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, map_sub, map_mul]
      by_cases h1 : i = c
      · subst h1; simp [hcj]
      · by_cases h2 : i = j₀
        · subst h2; simp [h1]; field_simp
        · simp [h1, h2]


lemma cv_single (j : Fin n) : cv F (Pi.single j (1 : 𝓞 F)) = Pi.single j 1 := by
  ext i; by_cases h : i = j
  · subst h; simp [cv]
  · simp [cv, h]

include hπ hv in
/-- **The columns of `nbMat` lie in $L(\vec v)$.** -/
lemma nbMat_col_mem {i₀ j₀ : Fin n} (hij : i₀ ≠ j₀) (c : Fin n) :
    nbMat π Q v i₀ j₀ *ᵥ Pi.single c 1 ∈ nbLat (K := F) Q π v := by
  classical
  rw [nbMat_col hπ hij]
  by_cases hci : c = i₀
  · rw [if_pos hci]; exact inv_smul_mem_nbLat hπ hv
  · rw [if_neg hci]
    by_cases hcj : c = j₀
    · rw [if_pos hcj, ← cv_single, ← cv_smul]; exact smul_cv_mem_nbLat hπ hv _
    · rw [if_neg hcj, cv_mem_nbLat_iff hπ hv, bv_eq_dot, sub_dotProduct, smul_dotProduct, smul_dotProduct,
        single_dotProduct, single_dotProduct, one_mul, one_mul, smul_eq_mul, smul_eq_mul, mul_comm, sub_self]
      exact dvd_zero π

lemma det_updateCol_one (i : Fin n) (w : Fin n → F) :
    ((1 : Matrix (Fin n) (Fin n) F).updateCol i w).det = w i := by
  rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl

include hπ in
/-- **`nbMat` has unit determinant at $\pi$**: $\det = \pi^{-1}v_{i_0}\cdot\pi\cdot\beta_{j_0}^{n-2}$. -/
lemma valuation_det_nbMat {i₀ j₀ : Fin n} (hi₀ : ¬ π ∣ v i₀)
    (hj₀ : ¬ π ∣ (Q.hessian *ᵥ v) j₀) : (hosOf hπ).valuation F (nbMat π Q v i₀ j₀).det = 1 := by
  classical
  set w := hosOf hπ
  have hunit : ∀ a : 𝓞 F, ¬ π ∣ a → w.valuation F (ιO a) = 1 := fun a ha => by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    change a ∉ Ideal.span {π}
    rwa [Ideal.mem_span_singleton]
  have hπ0 : w.valuation F (ιO π) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact πK_ne_zero hπ
  set r : Fin n → F := fun c => if c = j₀ then 1 else if c = i₀ then 0 else
    -(ιO ((Q.hessian *ᵥ v) c) / ιO π)
  have hU : ((1 : Matrix (Fin n) (Fin n) F).updateRow j₀ r).det = 1 := by
    have h1 := Matrix.updateRow_transpose (M := (1 : Matrix (Fin n) (Fin n) F)) (j := j₀) (c := r)
    rw [Matrix.transpose_one] at h1
    rw [h1, Matrix.det_transpose, det_updateCol_one]
    simp [r]
  have hprod : ∀ c ∈ Finset.univ, c ≠ j₀ → w.valuation F
      (if c = j₀ then ιO π else if c = i₀ then 1 else ιO ((Q.hessian *ᵥ v) j₀)) = 1 := by
    intro c _ hc
    rw [if_neg hc]
    split_ifs
    · exact map_one _
    · exact hunit _ hj₀
  rw [nbMat, Matrix.det_mul, Matrix.det_mul, hU, mul_one, det_updateCol_one, Matrix.det_diagonal,
    map_mul, map_prod, Finset.prod_eq_single j₀ hprod (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
  simp only [Pi.smul_apply, cv, smul_eq_mul, map_mul, map_inv₀, hunit _ hi₀, mul_one]
  exact inv_mul_cancel₀ hπ0


include hπ hv in
/-- The polar form is integral on $L(\vec v)$. -/
lemma bv_integral {x y : Fin n → F} (hx : x ∈ nbLat (K := F) Q π v) (hy : y ∈ nbLat (K := F) Q π v) :
    ∃ b : 𝓞 F, Nbr.bv F Q x y = ιO b := by
  obtain ⟨a, ha⟩ := nbLat_integral hπ hv x hx
  obtain ⟨c, hc⟩ := nbLat_integral hπ hv y hy
  obtain ⟨e, he⟩ := nbLat_integral hπ hv (x + y) (Submodule.add_mem _ hx hy)
  refine ⟨e - a - c, ?_⟩
  have h := Nbr.qv_add_smul (S := F) (Q := Q) x y 1
  rw [one_smul, one_mul, one_pow, one_mul] at h
  rw [map_sub, map_sub, ← he, ← ha, ← hc, h]; ring

lemma bv_sum_right (x : Fin n → F) (y : Fin n → F) (z : Fin n → Fin n → F) :
    Nbr.bv F Q x (∑ j, y j • z j) = ∑ j, y j * Nbr.bv F Q x (z j) := by
  simp only [Nbr.bv, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

lemma sum_smul_mulVec_single {K : Type*} [CommRing K] (g : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    ∑ j, y j • (g *ᵥ Pi.single j 1) = g *ᵥ y := by
  conv_rhs => rw [← Finset.univ_sum_single y]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_one]

include hπ hv in
/-- **Unimodular lattices are maximal integral** (the step $L(\vec v)_\pi \subseteq g\,\mathfrak o_\pi^n$): if the columns of $g$ lie in $L(\vec v)$,
their Gram matrix $G$ has $\det G$ a unit at $\pi$, then $g^{-1}x$ is $\pi$-integral for every $x \in L(\vec v)$ (Cramer: $G\,g^{-1}x =
(B(ge_i, x))_i$ is integral). -/
lemma valuation_inv_mulVec_le {g : Matrix (Fin n) (Fin n) F} (hg : IsUnit g)
    (hcol : ∀ c, g *ᵥ Pi.single c 1 ∈ nbLat (K := F) Q π v)
    (hG : (hosOf hπ).valuation F (Matrix.of fun i j =>
      Nbr.bv F Q (g *ᵥ Pi.single i 1) (g *ᵥ Pi.single j 1)).det = 1)
    {x : Fin n → F} (hx : x ∈ nbLat (K := F) Q π v) (i : Fin n) :
    (hosOf hπ).valuation F (((hg.unit⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ).val *ᵥ x) i) ≤ 1 := by
  classical
  set w := hosOf hπ
  set gcol := fun c => g *ᵥ Pi.single c 1
  set G : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => Nbr.bv F Q (gcol i) (gcol j)
  set y := (hg.unit⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ).val *ᵥ x
  have hgy : g *ᵥ y = x := by
    simp only [y, Matrix.mulVec_mulVec]
    rw [hg.mul_val_inv, Matrix.one_mulVec]
  have hGy : G *ᵥ y = fun i => Nbr.bv F Q (gcol i) x := by
    funext i
    rw [← hgy]
    conv_rhs => rw [← sum_smul_mulVec_single g y]
    rw [bv_sum_right]
    simp only [G, Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- integrality of `G` and of the right side
  have hGint : ∀ i j, ∃ b : 𝓞 F, G i j = ιO b := fun i j => bv_integral hπ hv (hcol i) (hcol j)
  have hbint : ∀ i, ∃ b : 𝓞 F, Nbr.bv F Q (gcol i) x = ιO b := fun i => bv_integral hπ hv (hcol i) hx
  choose G₀ hG₀ using hGint
  choose b₀ hb₀ using hbint
  have hGmap : G = (Matrix.of G₀).map ιO := by ext i j; exact hG₀ i j
  -- `det G • y = adj G *ᵥ b`
  have hadj : G.det • y = G.adjugate *ᵥ (fun i => Nbr.bv F Q (gcol i) x) := by
    rw [← hGy, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdet0 : G.det ≠ 0 := by
    intro h; rw [h, map_zero] at hG; exact zero_ne_one hG
  have hyi : y i = (G.det)⁻¹ * (G.adjugate *ᵥ (fun i => Nbr.bv F Q (gcol i) x)) i := by
    rw [← hadj, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdet0, one_mul]
  have hint : (G.adjugate *ᵥ (fun i => Nbr.bv F Q (gcol i) x)) i =
      ιO (((Matrix.of G₀).adjugate *ᵥ b₀) i) := by
    rw [hGmap, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate, RingHom.mapMatrix_apply,
      show (fun i => Nbr.bv F Q (gcol i) x) = fun i => ιO (b₀ i) from funext hb₀]
    exact (RingHom.map_mulVec ιO _ b₀ i).symm
  change w.valuation F (y i) ≤ 1
  rw [hyi, map_mul, map_inv₀, hG, inv_one, one_mul, hint, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _


lemma gram_eq (g : Matrix (Fin n) (Fin n) F) :
    (Matrix.of fun i j => Nbr.bv F Q (g *ᵥ Pi.single i 1) (g *ᵥ Pi.single j 1)) =
      gᵀ * Q.hessian.map ιO * g := by
  ext i j
  rw [Matrix.of_apply, Matrix.mulVec_single_one, Matrix.mulVec_single_one, Nbr.bv]
  simp only [dotProduct, Matrix.mulVec, Matrix.col_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

include hπ hdet hv hv0 in
/-- **The neighbour $L(\vec v)$ of $\mathcal O_F^n$ is free** for a prime element $\pi \nmid \det H$ (no class-number hypothesis): locally it is
$\mathfrak o_\mathfrak q^n$ at $\mathfrak q \ne (\pi)$ and $\gamma\,\mathfrak o_\pi^n$ with $\det\gamma$ a unit at $\pi$ (`nbMat`), so its Steinitz class is
trivial (`Steinitz.exists_latOf_of_loc`). -/
@[kb "kneser1957" "§1, the neighbour L(v) of O_F^n is free (any class number) [unverified]"]
theorem exists_latOf_nbLat : ∃ δ : GL (Fin n) F, latOf δ = nbLat (K := F) Q π v := by
  classical
  set N := nbLat (K := F) Q π v
  have h0 := πK_ne_zero (K := F) hπ
  -- `N` is a lattice
  have hNlat : N.IsLattice F := by
    have hstd : (intVec : Submodule (𝓞 F) (Fin n → F)).IsLattice F := intVec_isLattice
    set u : Fˣ := Units.mk0 _ h0
    have h1 : u • (intVec : Submodule (𝓞 F) (Fin n → F)) ≤ N := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hx
      rw [intVec_eq_stdLat] at hy
      obtain ⟨z, rfl⟩ := hy
      show (algebraMap (𝓞 F) F π) • cv F z ∈ N
      rw [← cv_smul]; exact smul_cv_mem_nbLat hπ hv z
    have h2' : N ≤ u⁻¹ • (intVec : Submodule (𝓞 F) (Fin n → F)) := by
      intro x hx
      obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hπ hx
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨cv F y, ?_, rfl⟩
      rw [intVec_eq_stdLat]; exact cv_mem_stdLat y
    have := hstd
    exact Submodule.IsLattice.of_le_of_isLattice_of_fg F h1
      (Submodule.FG.of_le (Submodule.IsLattice.fg (A := F) (M := u⁻¹ • intVec)) h2')
  cases n with
  | zero =>
    refine ⟨1, ?_⟩
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    simp only [Submodule.zero_mem]
  | succ m =>
    obtain ⟨i₀, j₀, hij, hi₀, hj₀⟩ := exists_coords hπ hdet hv hv0
    set g := nbMat π Q v i₀ j₀
    have hgdet := valuation_det_nbMat hπ (Q := Q) (v := v) (j₀ := j₀) hi₀ hj₀
    have hg : IsUnit g := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro h; rw [h, map_zero] at hgdet; exact zero_ne_one hgdet
    have hcol := nbMat_col_mem hπ hv hij (Q := Q)
    have hG : (hosOf hπ).valuation F (Matrix.of fun i j =>
        Nbr.bv F Q (g *ᵥ Pi.single i 1) (g *ᵥ Pi.single j 1)).det = 1 := by
      rw [gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, map_mul, map_mul, hgdet,
        show (Q.hessian.map ιO).det = ιO Q.hessian.det from (RingHom.map_det _ _).symm,
        HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_eq_one_iff.mpr (by
          change Q.hessian.det ∉ Ideal.span {π}; rwa [Ideal.mem_span_singleton])]
      simp
    obtain ⟨δ, hδ⟩ := Steinitz.exists_latOf_of_loc hNlat fun w => by
      by_cases hw : w = hosOf hπ
      · subst hw
        set U : GL (Fin (m + 1)) F := hg.unit
        refine ⟨Matrix.GeneralLinearGroup.map (algebraMap F ((hosOf hπ).adicCompletion F)) U, ?_, ?_⟩
        · apply le_antisymm
          · rintro _ ⟨z, hz, rfl⟩
            change (g.map (algebraMap F _)) *ᵥ z ∈ _
            rw [← sum_smul_mulVec_single]
            refine Submodule.sum_mem _ fun j _ => ?_
            have hzj : Valued.v (z j) ≤ 1 := by simpa using hz j
            have e : g.map (algebraMap F ((hosOf hπ).adicCompletion F)) *ᵥ Pi.single j 1 =
                locVec (hosOf hπ) (g *ᵥ Pi.single j 1) := by
              rw [locVec_mulVec, locVec_single, map_one]
            rw [e]
            exact Submodule.smul_mem _ (toO (hosOf hπ) (z j) hzj) (locVec_mem_loc _ (hcol j))
          · refine Submodule.span_le.mpr ?_
            rintro _ ⟨x, hx, rfl⟩
            refine mem_locAct.mpr ⟨locVec (hosOf hπ) ((U⁻¹ : GL (Fin (m + 1)) F).val *ᵥ x), fun i => ?_, ?_⟩
            · rw [neg_zero, WithZero.exp_zero, locVec_apply, valued_algebraMap]
              exact valuation_inv_mulVec_le hπ hv hg hcol hG hx i
            · change (U.val.map (algebraMap F _)) *ᵥ _ = _
              rw [← locVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
                Matrix.one_mulVec]
        · change Valued.v (g.map (algebraMap F _)).det = 1
          rw [show (g.map (algebraMap F ((hosOf hπ).adicCompletion F))).det =
              algebraMap F ((hosOf hπ).adicCompletion F) g.det from (RingHom.map_det _ _).symm,
            valued_algebraMap, hgdet]
      · refine ⟨1, ?_, by simp⟩
        rw [locAct_one, loc_nbLat_of_ne hπ Q hv w hw, loc_intVec]
    exact ⟨δ, hδ.symm⟩

variable [IsTotallyReal F]

@[kb "kneser1957" "Satz 1 (the neighbour lies in the genus), over F, any class number [unverified]"]
theorem sameGenus_glImage_nbLat' (Q : QuadForm F n) (γ : GL (Fin n) F) (hγ : IsIntegral Q (latOf γ))
    {π : 𝓞 F} (hπ : Prime π) (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ (gramZ Q γ hγ).hessian.det)
    {v : Fin n → 𝓞 F} (hv : π ^ 2 ∣ Nbr.qv (𝓞 F) (gramZ Q γ hγ) v) (hv0 : red π v ≠ 0) :
    SameGenus Q (latOf γ) (glImage γ (nbLat (K := F) (gramZ Q γ hγ) π v)) := by
  classical
  set Q' := gramZ Q γ hγ
  set N := nbLat (K := F) Q' π v
  have h0 := πK_ne_zero (K := F) hπ
  -- `N` is a lattice, hence free
  have hNlat : N.IsLattice F := by
    have hstd : (intVec : Submodule (𝓞 F) (Fin n → F)).IsLattice F := intVec_isLattice
    set u : Fˣ := Units.mk0 _ h0
    have h1 : u • (intVec : Submodule (𝓞 F) (Fin n → F)) ≤ N := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hx
      rw [intVec_eq_stdLat] at hy
      obtain ⟨z, rfl⟩ := hy
      show (algebraMap (𝓞 F) F π) • cv F z ∈ N
      rw [← cv_smul]; exact smul_cv_mem_nbLat hπ hv z
    have h2' : N ≤ u⁻¹ • (intVec : Submodule (𝓞 F) (Fin n → F)) := by
      intro x hx
      obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hπ hx
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨cv F y, ?_, rfl⟩
      rw [intVec_eq_stdLat]; exact cv_mem_stdLat y
    have := hstd
    exact Submodule.IsLattice.of_le_of_isLattice_of_fg F h1
      (Submodule.FG.of_le (Submodule.IsLattice.fg (A := F) (M := u⁻¹ • intVec)) h2')
  obtain ⟨δ, hδ'⟩ := exists_latOf_nbLat hπ hdet hv hv0
  have hδ : N = latOf δ := hδ'.symm
  -- integrality
  have hNint : IsIntegral (formF Q') (latOf δ) := by
    intro x hx
    rw [← hδ] at hx
    obtain ⟨z, hz⟩ := nbLat_integral hπ hv x hx
    rw [← qv_formF] at hz
    exact ⟨z, hz.symm⟩
  have hM' : glImage γ N = latOf (γ * δ) := by rw [latOf, glImage_mul, ← latOf, ← hδ]
  have hint' : IsIntegral Q (latOf (γ * δ)) := by
    rw [← hM']
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_glImage.mp hx
    obtain ⟨z, hz⟩ := nbLat_integral hπ hv y hy
    exact ⟨z, by rw [← qv_gramZ γ hγ]; exact hz.symm⟩
  rw [hM']
  intro w
  by_cases hw : w = hosOf hπ
  · -- at `π`: classification of unimodular forms
    subst hw
    apply exists_locAct_of_isometricGL (hosOf hπ) Q γ (γ * δ) hγ hint'
    have hπw := NF.irreducible_π (hosOf hπ)
    have h2w := NF.π_not_dvd_two (hosOf hπ) (two_not_mem hπ h2)
    -- the Gram form of `γδ` is that of `δ` for `Q'`
    have hG : gramZ Q (γ * δ) hint' = gramZ (formF Q') δ hNint := by
      refine QuadForm.ext_eval fun x => algebraMap_O_injective ?_
      rw [algebraMap_eval_gramZ, algebraMap_eval_gramZ, Units.val_mul, ← mulVec_mulVec]
      rw [show (formF Q').eval (δ.val *ᵥ intCoe x) = Nbr.qv F Q' (δ.val *ᵥ intCoe x) from qv_formF _ _,
        qv_gramZ]
    have hdet' : ¬ π ∣ (gramZ Q (γ * δ) hint').hessian.det := by
      rw [hG]; exact not_dvd_det_gramZ_nbLat hπ Q' hdet hv hv0 δ hδ.symm hNint
    refine isometricGL_of_unimodular_of_isometricIn hπw h2w ((hosOf hπ).adicCompletion F) _ _
      (by rw [NF.det_hessian_Qp, NF.π_dvd_ι_iff, hosOf_asIdeal, Ideal.mem_span_singleton]; exact hdet)
      (by rw [NF.det_hessian_Qp, NF.π_dvd_ι_iff, hosOf_asIdeal, Ideal.mem_span_singleton]; exact hdet')
      (GeneralLinearGroup.map (algebraMap F _) δ) fun x => ?_
    rw [evalIn_gramZ_map_completion, evalIn_gramZ_map_completion]
    change _ = Q.evalIn _ (γ.val.map _ *ᵥ (δ.val.map _ *ᵥ x))
    rw [mulVec_mulVec, ← Matrix.map_mul, Units.val_mul]
  · -- away from `π`: the localizations agree
    refine ⟨1, (orthGroup Q _).one_mem, ?_⟩
    rw [locAct_one, latOf, latOf, glImage_mul, loc_glImage, loc_glImage, ← latOf, ← hδ,
      loc_nbLat_of_ne hπ Q' hv w hw]

/-- **Kneser neighbours stay in the genus over $\mathcal O_F$** ($\pi$ a prime element of $\mathcal O_F$, $\pi \nmid 2\det H(Q_0)$, any class number; Kneser 1957, Satz 1
[unverified]; genus lattices are free by Steinitz): discharges `NbrInGenus Q₀ π`. -/
@[kb "kneser1957" "Satz 1 (neighbours lie in the genus), over F, principal primes, any class number [unverified]"]
theorem nbrInGenus' (Q₀ : QuadForm (𝓞 F) n) {π : 𝓞 F} (hπ : Prime π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q₀.hessian.det) : NbrInGenus Q₀ π := by
  classical
  intro M M' hl hg hN
  have := finite_res hπ
  let _ := Fintype.ofFinite (Res π)
  have hnd : (formF Q₀).Nondegenerate := by
    have e : (formF Q₀).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    show (formF Q₀).hessian.det ≠ 0
    rw [e, show (Q₀.hessian.map (algebraMap (𝓞 F) F)).det = algebraMap (𝓞 F) F Q₀.hessian.det from
      (RingHom.map_det _ _).symm, Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    rintro h0; exact hdet (h0 ▸ dvd_zero π)
  obtain ⟨γ, hγ⟩ := Steinitz.exists_latOf_of_sameGenus (formF Q₀) hnd hl hg
  subst hγ
  have hi : IsIntegral (formF Q₀) (latOf γ) := hN.int_left
  have hfs := formSameGenus_gramZ Q₀ hg hi
  have hdet' := not_dvd_det_of_formSameGenus hπ hfs hdet
  have hS := setOf_isNbrL_latOf (Q := formF Q₀) hπ γ hi hdet'
  have hmem : M' ∈ {M' | IsNbrL (formF Q₀) π (latOf γ) M'} := hN
  rw [hS] at hmem
  obtain ⟨N, hN', rfl⟩ := hmem
  unfold neighbors at hN'
  obtain ⟨vb, hvb, rfl⟩ := Finset.mem_image.mp hN'
  have := isMaximal_span hπ
  obtain ⟨h1, h2'⟩ := liftV_spec hπ hdet' hvb
  exact hg.trans _ (sameGenus_glImage_nbLat' (formF Q₀) γ hi hπ h2 hdet' h2'
    (by rw [h1]; exact (mem_isoSet.mp hvb).1))

end QuadFormsKB.HilbertModular.NeighborsNP