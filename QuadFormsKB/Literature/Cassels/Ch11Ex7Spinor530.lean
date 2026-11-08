/-
# Cassels, Ch. 11, Example 7 (i): the genus of $x^2 + xy + y^2 + 9z^2$ has two spinor genera

J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 11, Example 7 (i), p. 252 (`cassels1978`).

**Layer.** $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$ (`ex7f`), the lattice $\mathbb Z^3$ (`stdLat`), Cassels' group
$G = R/ST$ of (3.15) for $P = \{2, 3\}$ (`CasselsG`), whose order is the number of proper spinor genera
(`properSpinorGenusNumber_eq_card_casselsG`).

**Route.** $2f$ is the form `csQ A96` of Conway–Sloane's example (§9.6), whose local spinor norm groups are known
(`theta3_le`, `theta2_even`). Rescaling a form does not change the spinor norm of a rotation
(`spinorNorm_smul`: a rotation is a product of an even number of symmetries, and a symmetry does not change), so
$\theta(\Lambda_p)$ is the same for $f$ and $2f$ (`localSpinorNormGroup_smul`). Then $R = XT$, all units at $2$ lie
in $\theta(\Lambda_2)$ (Lemma 3.8, Cor.), every unit of $\mathbb Q_3$ is $\pm$ a square, so $G$ has at most the two
elements $1$ and the class of $\Delta_3(-1)$, which is nontrivial: the character "square class at $3$ modulo $3$"
kills $ST$ (`not_mem_casselsST_of_qClass`).
-/
import QuadFormsKB.Literature.Cassels.Ch11Examples4
import QuadFormsKB.Literature.Cassels.Ch11SpinorGeneraCount530
import QuadFormsKB.Literature.Cassels.Ch11Remarks2
import QuadFormsKB.Literature.ConwaySloane.Section9Example96
import QuadFormsKB.Literature.ConwaySloane.Section9TwoSpinorGenera
import QuadFormsKB.Literature.ConwaySloane.Section9Group

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Ex4

open QuadFormsKB QuadFormsKB.Lattices QuadFormsKB.ConwaySloane

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-! ### Rescaling the form does not change spinor norms of rotations -/

section Scaling

variable {n : ℕ} (Q : QuadForm ℚ n) (K : Type*) [Field K] [Algebra ℚ K] [CharZero K]

/-- $(aQ)(x) = a\,Q(x)$ over any $\mathbb Q$-algebra $K$. -/
theorem evalIn_smul_alg (a : ℚ) (x : Fin n → K) :
    (a • Q).evalIn K x = algebraMap ℚ K a * Q.evalIn K x := by
  rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, QuadForm.smul_coeff]
  have : (a • Q.coeff).map (algebraMap ℚ K) = algebraMap ℚ K a • Q.coeff.map (algebraMap ℚ K) := by
    ext i j; simp
  rw [this, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem hessian_smul_map (a : ℚ) :
    ((a • Q).hessian).map (algebraMap ℚ K) = algebraMap ℚ K a • Q.hessian.map (algebraMap ℚ K) := by
  rw [Lattices.ClassFin.hessian_smul]; ext i j; simp

variable {Q K}

theorem symmVec_smul {a : ℚ} (ha : a ≠ 0) {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) :
    symmVec (a • Q) K x = symmVec Q K x := by
  have ha' : algebraMap ℚ K a ≠ 0 := (map_ne_zero _).mpr ha
  rw [symmVec, symmVec, evalIn_smul_alg, hessian_smul_map, Matrix.smul_mulVec, mul_inv, smul_smul]
  congr 1
  field_simp

theorem symm_smul_val {a : ℚ} (ha : a ≠ 0) {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) :
    (((symm (a • Q) K x : orthGroup (a • Q) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((symm Q K x : orthGroup Q K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have ha' : algebraMap ℚ K a ≠ 0 := (map_ne_zero _).mpr ha
  have hx' : (a • Q).evalIn K x ≠ 0 := by rw [evalIn_smul_alg]; exact mul_ne_zero ha' hx
  rw [symm_val _ K hx', symm_val _ K hx, symmVec_smul ha hx]

theorem symmProd_smul_val {a : ℚ} (ha : a ≠ 0) :
    ∀ xs : List (Fin n → K), (∀ x ∈ xs, Q.evalIn K x ≠ 0) →
      (((symmProd (a • Q) K xs : orthGroup (a • Q) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (((symmProd Q K xs : orthGroup Q K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  | [], _ => by simp [symmProd]
  | x :: xs, h => by
    have h1 := symmProd_smul_val ha xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [symmProd, List.map_cons, List.prod_cons, Subgroup.coe_mul, Units.val_mul] at h1 ⊢
    rw [symm_smul_val ha (h x List.mem_cons_self), h1]

theorem valProd_smul {a : ℚ} :
    ∀ xs : List (Fin n → K), valProd (a • Q) K xs = algebraMap ℚ K a ^ xs.length * valProd Q K xs
  | [] => by simp [valProd]
  | x :: xs => by
    have h1 := valProd_smul (a := a) xs
    simp only [valProd, List.map_cons, List.prod_cons, List.length_cons] at h1 ⊢
    rw [evalIn_smul_alg, h1]; ring

/-- **Rescaling does not change the spinor norm of a rotation** ($a \ne 0$): a rotation $g$ of determinant $1$ is a
product $\tau_{x_1}\cdots\tau_{x_r}$ of an even number $r$ of symmetries; these are the same for $aQ$ and $Q$, and
$\prod aQ(x_i) = a^r\prod Q(x_i)$ with $r$ even. Arguments: `hQ`, `hQ'` the nondegeneracy of $Q$, $aQ$; `g` a
rotation of $Q$ and `g'` the same matrix as an isometry of $aQ$ (`hgg'`); `hdet`: $\det g = 1$. -/
theorem spinorNorm_smul (hQ : Q.Nondegenerate) {a : ℚ} (ha : a ≠ 0) (hQ' : (a • Q).Nondegenerate)
    (g : orthGroup Q K) (g' : orthGroup (a • Q) K)
    (hgg' : (g' : GL (Fin n) K) = (g : GL (Fin n) K))
    (hdet : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1) :
    spinorNorm (a • Q) K g' = spinorNorm Q K g := by
  obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q K hQ g
  have ha' : algebraMap ℚ K a ≠ 0 := (map_ne_zero _).mpr ha
  have hxs' : ∀ x ∈ xs, (a • Q).evalIn K x ≠ 0 := fun x hx => by
    rw [evalIn_smul_alg]; exact mul_ne_zero ha' (hxs x hx)
  have hg' : g' = symmProd (a • Q) K xs := Subtype.ext (Units.ext (by
    rw [hgg']; exact (symmProd_smul_val ha xs hxs).symm))
  have hev : Even xs.length := by
    have := det_symmProd Q xs hxs
    rw [this] at hdet
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hdet
  rw [hg', spinorNorm_symmProd _ K hQ' xs hxs', spinorNorm_symmProd _ K hQ xs hxs, valProd_smul]
  obtain ⟨m, hm⟩ := hev
  rw [hm, ← two_mul, mul_comm 2 m, pow_mul]
  exact sqClassOf_sq_mul (pow_ne_zero m ha') (valProd_ne_zero Q K hxs)

variable (K) in
theorem mem_orthGroup_smul_iff {a : ℚ} (ha : a ≠ 0) (g : GL (Fin n) K) :
    g ∈ orthGroup (a • Q) K ↔ g ∈ orthGroup Q K := by
  rw [ClassFin.orthGroup_smul Q ha K]

/-- Helper: one inclusion of local spinor norm groups for two forms $Q_1$, $Q_2$ with the same isometries and the same
spinor norms on rotations. Arguments: `h₁`, `h₂` nondegeneracy; `v` the prime; `L` the lattice; `hmem` equal
orthogonal groups; `hsn` equal spinor norms of a rotation. -/
theorem localSpinorNormGroup_le_of {Q₁ Q₂ : QuadForm ℚ n} (h₁ : Q₁.Nondegenerate) (h₂ : Q₂.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 ℚ)) (L : Lat ℚ n)
    (hmem : ∀ g : GL (Fin n) (v.adicCompletion ℚ), g ∈ orthGroup Q₁ (v.adicCompletion ℚ) →
      g ∈ orthGroup Q₂ (v.adicCompletion ℚ))
    (hsn : ∀ (g₁ : orthGroup Q₁ (v.adicCompletion ℚ)) (g₂ : orthGroup Q₂ (v.adicCompletion ℚ)),
      (g₁ : GL (Fin n) (v.adicCompletion ℚ)) = (g₂ : GL (Fin n) (v.adicCompletion ℚ)) →
      ((g₁ : GL (Fin n) (v.adicCompletion ℚ)) : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)).det = 1 →
      spinorNorm Q₁ (v.adicCompletion ℚ) g₁ = spinorNorm Q₂ (v.adicCompletion ℚ) g₂) :
    localSpinorNormGroup Q₁ h₁ v L ≤ localSpinorNormGroup Q₂ h₂ v L := by
  intro A hA
  rw [mem_localSpinorNormGroup] at hA ⊢
  obtain ⟨σ₁, ⟨hs, hd⟩, h⟩ := hA
  let σ₂ : orthGroup Q₂ (v.adicCompletion ℚ) := ⟨(σ₁ : GL (Fin n) (v.adicCompletion ℚ)), hmem _ σ₁.2⟩
  have hd₁ : ((σ₁ : GL (Fin n) (v.adicCompletion ℚ)) : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)).det = 1 :=
    Tamagawa.mem_soSub.mp hd
  have hs₁ : locAct v (σ₁ : GL (Fin n) (v.adicCompletion ℚ)) (loc v L.1) = loc v L.1 := hs
  have hs₂ : σ₂ ∈ locStabV Q₂ v L := hs₁
  have hd₂ : σ₂ ∈ Tamagawa.soSub Q₂ (v.adicCompletion ℚ) := Tamagawa.mem_soSub.mpr hd₁
  refine ⟨σ₂, ⟨hs₂, hd₂⟩, ?_⟩
  rw [← h]
  exact (hsn σ₁ σ₂ rfl hd₁).symm

/-- **Rescaling the form does not change the local spinor norm groups** ($a \ne 0$): $\theta(\Lambda_v)$ is the same
for $aQ$ as for $Q$, at every prime $v$ and for every lattice. Arguments: `hQ`, `hQ'` nondegeneracy of $Q$, $aQ$;
`v` the prime; `L` the lattice. -/
theorem localSpinorNormGroup_smul (hQ : Q.Nondegenerate) {a : ℚ} (ha : a ≠ 0) (hQ' : (a • Q).Nondegenerate)
    (v : HeightOneSpectrum (𝓞 ℚ)) (L : Lat ℚ n) :
    localSpinorNormGroup (a • Q) hQ' v L = localSpinorNormGroup Q hQ v L := by
  refine le_antisymm (localSpinorNormGroup_le_of hQ' hQ v L (fun g hg => (mem_orthGroup_smul_iff _ ha g).mp hg)
    fun g₁ g₂ he hd => spinorNorm_smul hQ ha hQ' g₂ g₁ he (he ▸ hd))
    (localSpinorNormGroup_le_of hQ hQ' v L (fun g hg => (mem_orthGroup_smul_iff _ ha g).mpr hg)
    fun g₁ g₂ he hd => (spinorNorm_smul hQ ha hQ' g₁ g₂ he.symm hd).symm)

end Scaling

end QuadFormsKB.Cassels.Ch11Ex4
