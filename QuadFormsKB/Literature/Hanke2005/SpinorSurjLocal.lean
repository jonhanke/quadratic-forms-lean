/-
# Local spinor norms of rotations (Shimura 1999, Lemma 2.2(1), non-archimedean and isotropic places)

**Layer:** the spinor norm $\sigma = \theta : O(V)(K)\to K^\times/K^{\times2}$ of `Lattices/SpinorNorm.lean`, for
$V = K^n$ with the form $Q$ = `Q : QuadForm F n` over a number field $F$, $K\supseteq F$ a field of characteristic $0$
(a completion of $F$).

Shimura (1999, Lemma 2.2(1), p. 7) states $\sigma(G_v) = W\cap F_v^\times$ for every place $v$, where $G = SO(V)$ and
$W = \{x\in F^\times_{\mathbb A} : x_v>0$ for every real place $v$ at which $G_v$ is compact$\}$ ($n>2$). His proof: "since
$\sigma(G_v)$ consists of the products $\varphi[x_1]\cdots\varphi[x_{2m}]$ with an even number of elements, we obtain (1) if
$v\in\mathbf a$ or $\varphi$ is isotropic at $v$"; at an anisotropic finite place ($n = 3, 4$) he uses quaternion algebras.

**Proves**
* `exists_so_spinorNorm_of_values`: if $Q(x) = c\,Q(y)\ne0$ then $\tau_x\tau_y\in SO(V)(K)$ has spinor norm $c\,K^{\times2}$;
* `exists_values_of_diag`: in diagonal coordinates $Q\simeq\langle b_0,\dots,b_{n-1}\rangle$, a nontrivial zero of
  $\langle b\rangle\perp\langle-cb\rangle$ gives $x, y$ with $Q(x) = c\,Q(y)\ne0$ (if the zero has $Q(y) = 0$, then $Q$ is
  isotropic, hence universal);
* `exists_so_spinorNorm_of_isotropic`: if $Q$ is isotropic over $K$, every $c\in K^\times$ is the spinor norm of a rotation;
* **`exists_so_spinorNorm_local`** (Lemma 2.2(1) at the finite places): for $n\ge3$ and every finite place $v$, every
  $c\in F_v^\times$ is the spinor norm of some $g\in SO(V)(F_v)$, i.e. $\sigma(G_v) = F_v^\times$.

*Route (differs from Shimura's at anisotropic places; purely local):* $\langle b\rangle\perp\langle-cb\rangle$ has rank
$2n\ge6\ge5$, so it is isotropic over the non-archimedean field $F_v$ (`LocalRankFive.isotropic_diag_five`); no
quaternion algebras are needed. All unconditional, standard axioms only.
-/
import QuadFormsKB.Lattices.SpinorGlobal
import QuadFormsKB.Tamagawa.LocalVolume

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.SpinorIdele

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section General

variable (Q : QuadForm F n) (K : Type*) [Field K] [Algebra F K] [CharZero K]

/-- **A rotation with prescribed spinor norm**: if $Q(y)\ne0$ and $Q(x) = c\,Q(y)$ with $c\ne0$, then
$g = \tau_x\tau_y\in SO(V)(K)$ and $\sigma(g) = Q(x)Q(y)\,K^{\times2} = c\,K^{\times2}$. -/
theorem exists_so_spinorNorm_of_values (hQ : Q.Nondegenerate) {c : K} (hc : c ≠ 0) {x y : Fin n → K}
    (hy : Q.evalIn K y ≠ 0) (hxy : Q.evalIn K x = c * Q.evalIn K y) :
    ∃ g ∈ soSub Q K, spinorNorm Q K g = sqClassOf c := by
  have hx : Q.evalIn K x ≠ 0 := by rw [hxy]; exact mul_ne_zero hc hy
  refine ⟨symm Q K x * symm Q K y, ?_, ?_⟩
  · rw [mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul, symm_det Q K hx, symm_det Q K hy]
    norm_num
  · have := spinorNorm_symmProd Q K hQ [x, y]
      (by intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          rcases hz with rfl | rfl <;> assumption)
    simp only [symmProd, valProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at this
    rw [this, hxy, mul_assoc, sqClassOf_mul hc (mul_ne_zero hy hy),
      (sqClassOf_eq_one_iff (mul_ne_zero hy hy)).mpr ⟨_, rfl⟩, mul_one]

/-- **Values $Q(x) = c\,Q(y)$ from a zero of $\langle b\rangle\perp\langle-cb\rangle$**: let $P$ (over $K$, invertible)
diagonalize $Q$, $Q(Pz) = \sum_ib_iz_i^2$ with all $b_i\ne0$. If $(x',y')\ne0$ and
$\sum_ib_ix_i'^2 = c\sum_ib_iy_i'^2$, then there are $x, y$ with $Q(y)\ne0$ and $Q(x) = c\,Q(y)$. -/
theorem exists_values_of_diag {b : Fin n → K} (hb : ∀ i, b i ≠ 0) {P : Matrix (Fin n) (Fin n) K}
    (hP : ∀ z, Q.evalIn K (P *ᵥ z) = ∑ i, b i * z i ^ 2) (c : K) {x' y' : Fin n → K}
    (hne : x' ≠ 0 ∨ y' ≠ 0) (hxy : ∑ i, b i * x' i ^ 2 = c * ∑ i, b i * y' i ^ 2) :
    ∃ x y : Fin n → K, Q.evalIn K y ≠ 0 ∧ Q.evalIn K x = c * Q.evalIn K y := by
  by_cases hy : ∑ i, b i * y' i ^ 2 = 0
  · -- the diagonal form is isotropic, hence universal
    have hiso : (QuadForm.diag b).IsotropicIn K := by
      rw [PadicClass.isotropicIn_diag_iff]
      rcases hne with h | h
      · exact ⟨x', h, by rw [hxy, hy, mul_zero]⟩
      · exact ⟨y', h, hy⟩
    obtain ⟨z1, hz1⟩ := PadicClass.representsIn_of_isotropic hb hiso c
    obtain ⟨z2, hz2⟩ := PadicClass.representsIn_of_isotropic hb hiso 1
    rw [PadicClass.evalIn_diag_self] at hz1 hz2
    refine ⟨P *ᵥ z1, P *ᵥ z2, ?_, ?_⟩
    · rw [hP, hz2]; simp
    · rw [hP, hP, hz1, hz2]; simp
  · exact ⟨P *ᵥ x', P *ᵥ y', by rw [hP]; exact hy, by rw [hP, hP]; exact hxy⟩

/-- Diagonal coordinates of $Q$ over $K$: $Q(Pz) = \sum_i b_iz_i^2$, $b_i\ne0$. -/
theorem exists_diag_coords (hQ : Q.Nondegenerate) :
    ∃ (b : Fin n → K) (P : Matrix (Fin n) (Fin n) K), (∀ i, b i ≠ 0) ∧
      ∀ z, Q.evalIn K (P *ᵥ z) = ∑ i, b i * z i ^ 2 := by
  obtain ⟨b, hb, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  obtain ⟨P, -, hP⟩ := FieldGen.isometricIn_of_base K hiso
  refine ⟨fun i => algebraMap F K (b i), P, fun i => (map_ne_zero _).mpr (hb i), fun z => ?_⟩
  rw [hP, QuadForm.evalIn_diag]

/-- **Isotropic places** (Shimura 1999, Lemma 2.2(1), "if $\varphi$ is isotropic at $v$"): if $Q$ is isotropic over $K$,
every $c\in K^\times$ is the spinor norm of a rotation, $\sigma(SO(V)(K)) = K^\times$. -/
@[kb "shimura1999" "Lemma 2.2(1), p. 7 (isotropic places)"]
theorem exists_so_spinorNorm_of_isotropic (hQ : Q.Nondegenerate) (hiso : Q.IsotropicIn K) {c : K} (hc : c ≠ 0) :
    ∃ g ∈ soSub Q K, spinorNorm Q K g = sqClassOf c := by
  obtain ⟨b, P, hb, hP⟩ := exists_diag_coords Q K hQ
  obtain ⟨x0, hx0, hQx0⟩ := hiso
  -- `x0 = P z0` with `z0 ≠ 0` an isotropic vector of the diagonal form
  obtain ⟨b', hb', hiso'⟩ := FieldGen.exists_isometric_diag Q hQ
  obtain ⟨P', hP'u, hP'⟩ := FieldGen.isometricIn_of_base K hiso'
  have hdiag : (QuadForm.diag b').IsotropicIn K := by
    obtain ⟨u, hu⟩ := hP'u
    refine ⟨(↑u⁻¹ : K) • (P'.adjugate *ᵥ x0), ?_, ?_⟩
    · intro h
      apply hx0
      have h2 : P' *ᵥ ((↑u⁻¹ : K) • (P'.adjugate *ᵥ x0)) = x0 := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, ← hu, Matrix.smul_mulVec,
          Matrix.one_mulVec, smul_smul, Units.inv_mul, one_smul]
      rw [← h2, h, Matrix.mulVec_zero]
    · have h2 : P' *ᵥ ((↑u⁻¹ : K) • (P'.adjugate *ᵥ x0)) = x0 := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, ← hu, Matrix.smul_mulVec,
          Matrix.one_mulVec, smul_smul, Units.inv_mul, one_smul]
      rw [← hP', h2, hQx0]
  have hb'K : ∀ i, algebraMap F K (b' i) ≠ 0 := fun i => (map_ne_zero _).mpr (hb' i)
  have hdiagK : (QuadForm.diag fun i => algebraMap F K (b' i)).IsotropicIn K := by
    obtain ⟨z, hz0, hz⟩ := hdiag
    refine ⟨z, hz0, ?_⟩
    rw [PadicClass.evalIn_diag_self]; rw [QuadForm.evalIn_diag] at hz; exact hz
  obtain ⟨z1, hz1⟩ := PadicClass.representsIn_of_isotropic hb'K hdiagK c
  obtain ⟨z2, hz2⟩ := PadicClass.representsIn_of_isotropic hb'K hdiagK 1
  rw [PadicClass.evalIn_diag_self] at hz1 hz2
  have hPz : ∀ z, Q.evalIn K (P' *ᵥ z) = ∑ i, algebraMap F K (b' i) * z i ^ 2 := fun z => by
    rw [hP', QuadForm.evalIn_diag]
  refine exists_so_spinorNorm_of_values Q K hQ hc (x := P' *ᵥ z1) (y := P' *ᵥ z2) ?_ ?_
  · rw [hPz, hz2]; simp
  · rw [hPz, hPz, hz1, hz2]; simp

end General

section Local

variable (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **Shimura 1999, Lemma 2.2(1), at the finite places**: for $Q$ nondegenerate in $n\ge3$ variables and every finite
place $v$, every $c\in F_v^\times$ is the spinor norm of a rotation: $\sigma(SO(V)(F_v)) = F_v^\times$ (for $n>2$,
$W\cap F_v^\times = F_v^\times$ at finite $v$). -/
@[kb "shimura1999" "Lemma 2.2(1), p. 7 (finite places, n > 2)"]
theorem exists_so_spinorNorm_local (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {c : Fv} (hc : c ≠ 0) :
    ∃ g ∈ soSub Q Fv, spinorNorm Q Fv g = sqClassOf c := by
  obtain ⟨b, P, hb, hP⟩ := exists_diag_coords Q Fv hQ
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  obtain ⟨z, hz0, hz⟩ := LocalRankFive.isotropic_diag_five v ![b i0, b i1, b i2, -c * b i0, -c * b i1]
    (by intro i; fin_cases i <;> simp [hb, hc])
  rw [PadicClass.evalIn_diag_self, Fin.sum_univ_five] at hz
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at hz
  set x' : Fin n → Fv := Pi.single i0 (z 0) + Pi.single i1 (z 1) + Pi.single i2 (z 2)
  set y' : Fin n → Fv := Pi.single i0 (z 3) + Pi.single i1 (z 4)
  have hsx : ∑ i, b i * x' i ^ 2 = b i0 * z 0 ^ 2 + b i1 * z 1 ^ 2 + b i2 * z 2 ^ 2 := by
    have : ∀ i, b i * x' i ^ 2 = (if i = i0 then b i0 * z 0 ^ 2 else 0) + (if i = i1 then b i1 * z 1 ^ 2 else 0) +
        (if i = i2 then b i2 * z 2 ^ 2 else 0) := by
      intro i
      by_cases e0 : i = i0
      · subst e0; simp [x', h01, h02]
      · by_cases e1 : i = i1
        · subst e1; simp [x', h01.symm, h12]
        · by_cases e2 : i = i2
          · subst e2; simp [x', h02.symm, h12.symm]
          · simp [x', e0, e1, e2]
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp [Finset.sum_add_distrib]
  have hsy : ∑ i, b i * y' i ^ 2 = b i0 * z 3 ^ 2 + b i1 * z 4 ^ 2 := by
    have : ∀ i, b i * y' i ^ 2 = (if i = i0 then b i0 * z 3 ^ 2 else 0) + (if i = i1 then b i1 * z 4 ^ 2 else 0) := by
      intro i
      by_cases e0 : i = i0
      · subst e0; simp [y', h01]
      · by_cases e1 : i = i1
        · subst e1; simp [y', h01.symm]
        · simp [y', e0, e1]
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp [Finset.sum_add_distrib]
  have hne : x' ≠ 0 ∨ y' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hx, hy⟩ := hcon
    apply hz0
    have e0 := congrFun hx i0; have e1 := congrFun hx i1; have e2 := congrFun hx i2
    have f0 := congrFun hy i0; have f1 := congrFun hy i1
    simp [x', y', h01, h02, h12, h01.symm, h02.symm, h12.symm] at e0 e1 e2 f0 f1
    funext i; fin_cases i <;> simp [e0, e1, e2, f0, f1]
  obtain ⟨x, y, hy, hxy⟩ := exists_values_of_diag Q Fv hb hP c hne (by
    rw [hsx, hsy]; linear_combination hz)
  exact exists_so_spinorNorm_of_values Q Fv hQ hc hy hxy

end Local

end QuadFormsKB.Hanke2005.SpinorIdele
