/-
# Cassels, Chapter 8, Corollaries 1 and 2 to Lemma 3.3: integral automorphs are products of symmetries

**Setting** (as in `Ch8/Bases.lean`): $p \ne 2$, a regular form $f(\vec x) = \vec x^{t}F\vec x$ with symmetric
$F \in M_n(\mathbb Q_p)$, $\det F \ne 0$; integral automorphs (`IsIntAut`) and the symmetries $\tau_b$ (`tauFun`,
`tau`) of Cassels' (3.7). A product $\tau_{b_1}\cdots\tau_{b_k}$ is the product of the list
`[tauFun F b₁, …, tauFun F bₖ]` in the ring of $\mathbb Q_p$-linear endomorphisms (composition, $\tau_{b_k}$ applied
first).

**Proves**
* `intAut_eq_prod_tau` (**Corollary 1**, p. 115): every integral automorph is a product of integral automorphs
  $\tau_b$ with $\vec b$ integral;
* `intAut_eq_prod_tau_unit` (**Corollary 2**, p. 115): if moreover $f$ is integral with unit determinant, the $\vec b$
  can be taken with $f(\vec b)$ a $p$-adic unit.

**Proof.** Not Cassels' induction on the dimension, but O'Meara's Theorem 92:4 (`OMeara.exists_symmetry_list`, the same
argument: Lemma 3.3 and induction) applied to the lattice $\mathbb Z_p^n$ in the quadratic space
$(\mathbb Q_p^n, f)$; the bridge to O'Meara's notation is in `Ch8/LatticeBridge.lean`.
-/
import QuadFormsKB.Literature.Cassels.Ch8.LatticeBridge

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- $\lVert 2\rVert_p = 1$ for $p \ne 2$. -/
private theorem norm_two_padic (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  have : (2 : ℚ_[p]) = ((2 : ℕ) : ℚ_[p]) := by norm_num
  rw [this, Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes hp.out Nat.prime_two).2 hp2

/-- A nonzero vector has a scalar multiple in $\mathbb Z_p^n$ with a coordinate of norm $1$. -/
private theorem exists_prim {b : Fin n → ℚ_[p]} (hb : b ≠ 0) :
    ∃ c : ℚ_[p], c ≠ 0 ∧ IsIntVec (c • b) ∧ ∃ i, ‖(c • b) i‖ = 1 := by
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
    by_contra h
    push Not at h
    exact hb (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖b i‖) ⟨j, Finset.mem_univ j⟩
  have hbi : b i ≠ 0 := by
    intro h
    have := hi j (Finset.mem_univ j)
    rw [h, norm_zero] at this
    exact hj (norm_le_zero_iff.1 this)
  have hpos : 0 < ‖b i‖ := norm_pos_iff.2 hbi
  refine ⟨(b i)⁻¹, inv_ne_zero hbi, fun k => ?_, i, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    rw [inv_mul_le_iff₀ hpos]
    simpa using hi k (Finset.mem_univ k)
  · simp [norm_inv, hpos.ne']

private theorem tauFun_smul (F : Matrix (Fin n) (Fin n) ℚ_[p]) {c : ℚ_[p]} (hc : c ≠ 0) (u x : Fin n → ℚ_[p]) :
    tauFun F (c • u) x = tauFun F u x := by
  have hb : bil F (c • u) x = c * bil F u x := by
    simp only [bil, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
  have hq : qf F (c • u) = c ^ 2 * qf F u := by
    simp only [qf, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
  rw [tauFun_apply, tauFun_apply, hb, hq, smul_smul]
  by_cases h0 : qf F u = 0
  · simp [h0]
  · rw [show c * bil F u x / (c ^ 2 * qf F u) * c = bil F u x / qf F u by field_simp]

private theorem qf_smul' (F : Matrix (Fin n) (Fin n) ℚ_[p]) (c : ℚ_[p]) (u : Fin n → ℚ_[p]) :
    qf F (c • u) = c ^ 2 * qf F u := by
  simp only [qf, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring

/-- Scaling the vector does not change the integral symmetry. -/
private theorem tau_smul (F : Matrix (Fin n) (Fin n) ℚ_[p]) {c : ℚ_[p]} (hc : c ≠ 0) {u : Fin n → ℚ_[p]}
    (hu : qf F u ≠ 0) (hcu : qf F (c • u) ≠ 0) : tau F hcu = tau F hu :=
  LinearEquiv.ext fun x => tauFun_smul F hc u x

/-- The symmetry $\tau_u$ is an integral automorph when O'Meara's symmetry lies in $O(\mathbb Z_p^n)$. -/
private theorem isIntAut_tau_of_mem {F : Matrix (Fin n) (Fin n) ℚ_[p]} (hF : Fᵀ = F) {u : Fin n → ℚ_[p]}
    (hu : qfForm F u ≠ 0) (hq : qf F u ≠ 0)
    (h : OMeara.symmetry (qfForm F) u hu ∈ OMeara.orthLat (qfForm F) (zpLat p n)) : IsIntAut F (tau F hq) := by
  have : tau F hq = OMeara.symmetry (qfForm F) u hu :=
    LinearEquiv.ext fun x => (symmetry_eq_tauFun hF hu x).symm
  rw [this]
  exact (isIntAut_iff_mem_orthLat F _).2 h

/-- **Cassels, Ch. 8, Corollary 1 to Lemma 3.3** ($p \ne 2$): *let $\sigma$ be any integral automorph of $f(\vec x)$.
Then $\sigma$ is the product of integral automorphs $\tau_b$ with integral $\vec b$.* Here $f$ is regular
($F^{t} = F$, $\det F \ne 0$, as throughout Cassels' §3); each $\vec b$ in the list is integral (`IsIntVec`), has
$f(\vec b) \ne 0$, and $\tau_b$ is an integral automorph; $\sigma$ is the product of the $\tau_b$ in list order. -/
@[kb "cassels1978" "Ch. 8, Cor. 1 to Lemma 3.3, p. 115"]
theorem intAut_eq_prod_tau (hp2 : p ≠ 2) (F : Matrix (Fin n) (Fin n) ℚ_[p]) (hF : Fᵀ = F) (hdet : F.det ≠ 0)
    {σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p])} (hσ : IsIntAut F σ) :
    ∃ l : List (Fin n → ℚ_[p]), (∀ b ∈ l, IsIntVec b ∧ ∃ hb : qf F b ≠ 0, IsIntAut F (tau F hb)) ∧
      σ.toLinearMap = (l.map (tauFun F)).prod := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨[], by simp, ?_⟩
    exact LinearMap.ext fun x => Subsingleton.elim _ _
  have h2 : IsUnit (2 : ℤ_[p]) := by
    have : (2 : ℤ_[p]) = ((2 : ℕ) : ℤ_[p]) := by norm_num
    rw [this, PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hp.out Nat.prime_two).2 hp2
  have hright : ∀ y : Fin n → ℚ_[p], (∀ x, OMeara.bil (qfForm F) x y = 0) → y = 0 := by
    intro y hy
    refine Matrix.eq_zero_of_mulVec_eq_zero hdet (funext fun i => ?_)
    have := hy (Pi.single i 1)
    rw [bil_qfForm hF, single_dotProduct, one_mul] at this
    simpa using this
  have hV : (QuadraticMap.associated (qfForm F)).Nondegenerate :=
    ⟨fun x hx => hright x fun z => (OMeara.bil_comm (qfForm F) z x).trans (hx z), hright⟩
  have hn' : 1 ≤ Module.finrank ℚ_[p] (Fin n → ℚ_[p]) := by
    rw [Module.finrank_fin_fun]; exact hn
  obtain ⟨l, -, hl, hσl⟩ := OMeara.exists_symmetry_list (R := ℤ_[p]) (F := ℚ_[p]) (qfForm F) h2 hV hn'
    zpLat_isLattice ((isIntAut_iff_mem_orthLat F σ).1 hσ)
  have hscale : ∀ u : Fin n → ℚ_[p], ∃ c : ℚ_[p], (u ≠ 0 → c ≠ 0 ∧ IsIntVec (c • u)) := by
    intro u
    by_cases hu : u = 0
    · exact ⟨1, fun h => absurd hu h⟩
    · obtain ⟨c, hc, hci, -⟩ := exists_prim hu
      exact ⟨c, fun _ => ⟨hc, hci⟩⟩
  choose s hs using hscale
  have hne : ∀ u ∈ l, qf F u ≠ 0 ∧ u ≠ 0 := by
    intro u hu
    obtain ⟨hQ, -⟩ := hl u hu
    have hq : qf F u ≠ 0 := by rwa [← qfForm_apply]
    exact ⟨hq, fun h0 => hq (by rw [h0]; simp [qf])⟩
  refine ⟨l.map fun u => s u • u, ?_, ?_⟩
  · intro b hb
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hb
    obtain ⟨hq, hu0⟩ := hne u hu
    obtain ⟨hQ, hsym⟩ := hl u hu
    obtain ⟨hc, hci⟩ := hs u hu0
    have hq' : qf F (s u • u) ≠ 0 := by
      rw [qf_smul']; exact mul_ne_zero (pow_ne_zero 2 hc) hq
    refine ⟨hci, hq', ?_⟩
    rw [tau_smul F hc hq hq']
    exact isIntAut_tau_of_mem hF hQ hq hsym
  · have hmap := map_list_prod (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ℚ_[p])
      (M := Fin n → ℚ_[p])) (l.map (OMeara.symmetryOrOne (qfForm F)))
    have hcongr : (l.map (OMeara.symmetryOrOne (qfForm F))).map
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ℚ_[p]) (M := Fin n → ℚ_[p])) =
        (l.map fun u => s u • u).map (tauFun F) := by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun u hu => ?_
      obtain ⟨hq, hu0⟩ := hne u hu
      obtain ⟨hQ, -⟩ := hl u hu
      obtain ⟨hc, -⟩ := hs u hu0
      refine LinearMap.ext fun x => ?_
      show OMeara.symmetryOrOne (qfForm F) u x = tauFun F (s u • u) x
      rw [OMeara.sym4_symmetryOrOne_of_ne _ hQ, symmetry_eq_tauFun hF hQ, tauFun_smul F hc]
    rw [← hcongr, ← hmap]
    conv_lhs => rw [hσl]
    rfl

/-- For symmetric $F$, $\vec u^{t}F\vec x = \vec x^{t}F\vec u$. -/
private theorem dot_mulVec_symm {F : Matrix (Fin n) (Fin n) ℚ_[p]} (hF : Fᵀ = F) (u x : Fin n → ℚ_[p]) :
    u ⬝ᵥ F *ᵥ x = x ⬝ᵥ F *ᵥ u := by
  have : u ᵥ* F = F *ᵥ u := by rw [← Matrix.vecMul_transpose, hF]
  rw [Matrix.dotProduct_mulVec, this, dotProduct_comm]

/-- Over $\mathbb Z_p$: if $\det F_0$ is a unit and $b_0$ has a unit coordinate, so does $F_0b_0$. -/
private theorem exists_unit_coord {F₀ : Matrix (Fin n) (Fin n) ℤ_[p]} (hunit : IsUnit F₀.det)
    (b₀ : Fin n → ℤ_[p]) {i₀ : Fin n} (h0 : IsUnit (b₀ i₀)) : ∃ i, IsUnit ((F₀ *ᵥ b₀) i) := by
  by_contra hno
  push Not at hno
  have hb : b₀ = F₀⁻¹ *ᵥ (F₀ *ᵥ b₀) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  have h1 : b₀ i₀ = ∑ j, F₀⁻¹ i₀ j * (F₀ *ᵥ b₀) j := congrFun hb i₀
  have hmem : b₀ i₀ ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [h1]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hno j))
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem h0

/-- For a primitive integral $\vec b$ with $\tau_b$ integral, $f$ integral of unit determinant: $\lvert f(\vec b)\rvert = 1$. -/
private theorem norm_qf_eq_one (hp2 : p ≠ 2) (F : Matrix (Fin n) (Fin n) ℚ_[p]) (hF : Fᵀ = F)
    (hint : ∀ i j, ‖F i j‖ ≤ 1) (hdet : ‖F.det‖ = 1) {b : Fin n → ℚ_[p]} (hbi : IsIntVec b) {i₀ : Fin n}
    (hi₀ : ‖b i₀‖ = 1) (hq : qf F b ≠ 0) (haut : IsIntAut F (tau F hq)) : ‖qf F b‖ = 1 := by
  classical
  set φ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom with hφ
  let F₀ : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of fun i j => ⟨F i j, hint i j⟩
  have hF₀ : F₀.map φ = F := by ext i j; rfl
  have hunit : IsUnit F₀.det := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_def]
    have h := RingHom.map_det φ F₀
    have e : (φ.mapMatrix F₀) = F := hF₀
    rw [e] at h
    show ‖φ F₀.det‖ = 1
    rw [h]; exact hdet
  let b₀ : Fin n → ℤ_[p] := fun i => ⟨b i, hbi i⟩
  have hb₀ : toQ b₀ = b := rfl
  have hv : toQ (F₀ *ᵥ b₀) = F₀.map φ *ᵥ toQ b₀ := by
    funext k; exact RingHom.map_mulVec φ F₀ b₀ k
  rw [hF₀, hb₀] at hv
  obtain ⟨i, hi⟩ := exists_unit_coord hunit b₀ (i₀ := i₀) (PadicInt.isUnit_iff.2 hi₀)
  have hi1 : ‖(F *ᵥ b) i‖ = 1 := by
    rw [← hv]; exact PadicInt.isUnit_iff.1 hi
  have hx : IsIntVec (Pi.single i (1 : ℚ_[p]) : Fin n → ℚ_[p]) := by
    intro j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  have hbil : bil F b (Pi.single i (1 : ℚ_[p])) = 2 * (F *ᵥ b) i := by
    have hs := dot_mulVec_symm hF b (Pi.single i (1 : ℚ_[p]))
    simp only [bil, hs, single_dotProduct, one_mul]; ring
  have hbn : ‖bil F b (Pi.single i (1 : ℚ_[p]))‖ = 1 := by
    rw [hbil, norm_mul, norm_two_padic hp2, hi1, mul_one]
  have hout := haut.2.1 _ hx i₀
  have hte : (tau F hq) (Pi.single i (1 : ℚ_[p])) = tauFun F b (Pi.single i (1 : ℚ_[p])) := rfl
  rw [hte, tauFun_apply] at hout
  have hout' : ‖(Pi.single i (1 : ℚ_[p]) : Fin n → ℚ_[p]) i₀ -
      (bil F b (Pi.single i (1 : ℚ_[p])) / qf F b) * b i₀‖ ≤ 1 := by simpa using hout
  have h3 : ‖(bil F b (Pi.single i (1 : ℚ_[p])) / qf F b) * b i₀‖ ≤ 1 := by
    have e : (bil F b (Pi.single i (1 : ℚ_[p])) / qf F b) * b i₀ =
        (Pi.single i (1 : ℚ_[p]) : Fin n → ℚ_[p]) i₀ -
          ((Pi.single i (1 : ℚ_[p]) : Fin n → ℚ_[p]) i₀ -
            (bil F b (Pi.single i (1 : ℚ_[p])) / qf F b) * b i₀) := by ring
    rw [e, sub_eq_add_neg]
    refine (Padic.nonarchimedean _ _).trans (max_le (hx i₀) ?_)
    rwa [norm_neg]
  rw [norm_mul, hi₀, mul_one, norm_div, div_le_one (norm_pos_iff.2 hq), hbn] at h3
  have hup : ‖qf F b‖ ≤ 1 := by
    have e : qf F b = φ (b₀ ⬝ᵥ (F₀ *ᵥ b₀)) := by
      unfold qf
      rw [RingHom.map_dotProduct]
      exact congrArg (fun w => b ⬝ᵥ w) hv.symm
    rw [e]
    exact PadicInt.norm_le_one _
  exact le_antisymm hup h3

/-- **Cassels, Ch. 8, Corollary 2 to Lemma 3.3** ($p \ne 2$): *suppose, further, that $f(\vec x)$ is integral and that
its determinant is a $p$-adic unit. Then any integral automorph $\sigma$ of $f(\vec x)$ is a product of $\tau_b$ where
$\vec b$ is integral and $f(\vec b)$ is a $p$-adic unit (so $\tau_b$ is integral).* Integral is classical integrality
$\lvert f_{ij}\rvert_p \le 1$; the determinant is $d(f) = \det F$. -/
@[kb "cassels1978" "Ch. 8, Cor. 2 to Lemma 3.3, p. 115"]
theorem intAut_eq_prod_tau_unit (hp2 : p ≠ 2) (F : Matrix (Fin n) (Fin n) ℚ_[p]) (hF : Fᵀ = F)
    (hint : ∀ i j, ‖F i j‖ ≤ 1) (hdet : ‖F.det‖ = 1)
    {σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p])} (hσ : IsIntAut F σ) :
    ∃ l : List (Fin n → ℚ_[p]), (∀ b ∈ l, IsIntVec b ∧ ‖qf F b‖ = 1 ∧ ∃ hb : qf F b ≠ 0, IsIntAut F (tau F hb)) ∧
      σ.toLinearMap = (l.map (tauFun F)).prod := by
  classical
  have hdet0 : F.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨l, hl, hσl⟩ := intAut_eq_prod_tau hp2 F hF hdet0 hσ
  have hscale : ∀ u : Fin n → ℚ_[p], ∃ c : ℚ_[p],
      (u ≠ 0 → c ≠ 0 ∧ IsIntVec (c • u) ∧ ∃ i, ‖(c • u) i‖ = 1) := by
    intro u
    by_cases hu : u = 0
    · exact ⟨1, fun h => absurd hu h⟩
    · obtain ⟨c, hc, hci, hi⟩ := exists_prim hu
      exact ⟨c, fun _ => ⟨hc, hci, hi⟩⟩
  choose s hs using hscale
  have hne : ∀ u ∈ l, qf F u ≠ 0 ∧ u ≠ 0 := by
    intro u hu
    obtain ⟨-, hq, -⟩ := hl u hu
    exact ⟨hq, fun h0 => hq (by rw [h0]; simp [qf])⟩
  refine ⟨l.map fun u => s u • u, ?_, ?_⟩
  · intro b hb
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hb
    obtain ⟨hq, hu0⟩ := hne u hu
    obtain ⟨-, hq0, haut⟩ := hl u hu
    obtain ⟨hc, hci, i₀, hi₀⟩ := hs u hu0
    have hq' : qf F (s u • u) ≠ 0 := by
      rw [qf_smul']; exact mul_ne_zero (pow_ne_zero 2 hc) hq
    have haut' : IsIntAut F (tau F hq') := by
      rw [tau_smul F hc hq0 hq']; exact haut
    exact ⟨hci, norm_qf_eq_one hp2 F hF hint hdet hci hi₀ hq' haut', hq', haut'⟩
  · rw [hσl, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    obtain ⟨-, hu0⟩ := hne u hu
    obtain ⟨hc, -⟩ := hs u hu0
    refine LinearMap.ext fun x => ?_
    exact (tauFun_smul F hc u x).symm

end QuadFormsKB.Cassels
