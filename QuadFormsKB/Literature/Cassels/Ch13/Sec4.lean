import Mathlib
import QuadFormsKB.Citation

/-!
# Cassels, Chapter 13, §4: commensurability of integral automorph groups (Lemma 4.1)

Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §4 (*Construction of automorphs*), p. 300.

**Setting.** A form is $f(\vec{x}) = \vec{x}^{\mathsf T}F\vec{x}$ with $F$ a rational $n\times n$ matrix; its integral
automorphs form $O(f) \le GL_n(\mathbb Z)$ (`autZ`). For $S \in GL_n(\mathbb Q)$, $g(\vec{x}) = f(S\vec{x})$ has matrix
$S^{\mathsf T}FS$.

**What is proved.** Lemma 4.1 (`lemma_4_1`): $T \mapsto S^{-1}TS$ maps the $T \in O(f)$ with integral conjugate
into $O(g)$, and both the set of such $T$ and the set of the resulting $U$ are subgroups of finite index.

**Proof notes.** As in Cassels: the subgroup contains the congruence subgroup $\Gamma(s_1s_2)$ (`gamma`), where
$s_1S^{-1}$ and $s_2S$ are integral (`exists_den`); $\Gamma(N)$ is the kernel of reduction to the finite group
$GL_n(\mathbb Z/N)$. "Integral" is read as "in $GL_n(\mathbb Z)$"; an integral conjugate of $T$ automatically has
determinant $\det T = \pm1$ (shown inside `gamma_le_conjIntegral`).
-/

open Matrix

namespace QuadFormsKB.Cassels.Ch13

variable {n : ℕ}

/-- An integral $n\times n$ matrix viewed as a rational matrix. -/
abbrev castQ (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ := A.map (Int.castRingHom ℚ)

/-- The inclusion $GL_n(\mathbb Z) \to GL_n(\mathbb Q)$ (Cassels' $SL^{\pm}_n(\mathbb Z)$: integral matrices of determinant $\pm1$). -/
def glCast : GL (Fin n) ℤ →* GL (Fin n) ℚ := Units.map (RingHom.mapMatrix (Int.castRingHom ℚ)).toMonoidHom

/-- The matrix of `glCast T` is $T$ read over $\mathbb Q$. -/
theorem coe_glCast (T : GL (Fin n) ℤ) : ((glCast T : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) = castQ T := rfl

/-- The group $O_{\mathbb Q}(f)$ of rational automorphs of the form $f(\vec{x}) = \vec{x}^{\mathsf T}F\vec{x}$: the $A \in GL_n(\mathbb Q)$ with $A^{\mathsf T}FA = F$. -/
def orthoQ (F : Matrix (Fin n) (Fin n) ℚ) : Subgroup (GL (Fin n) ℚ) where
  carrier := {A | (A : Matrix (Fin n) (Fin n) ℚ)ᵀ * F * A = F}
  mul_mem' {A B} hA hB := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, transpose_mul] at *
    calc (B : Matrix (Fin n) (Fin n) ℚ)ᵀ * (A : Matrix (Fin n) (Fin n) ℚ)ᵀ * F * (A * B)
        = (B : Matrix (Fin n) (Fin n) ℚ)ᵀ * ((A : Matrix (Fin n) (Fin n) ℚ)ᵀ * F * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = F := by rw [hA, hB]
  one_mem' := by simp
  inv_mem' {A} hA := by
    simp only [Set.mem_ofPred_eq] at *
    obtain ⟨a, ha⟩ : ∃ a, a = (A : Matrix (Fin n) (Fin n) ℚ) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = ((A⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) := ⟨_, rfl⟩
    have hab : a * b = 1 := by rw [ha, hb, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← ha] at hA
    rw [← hb]
    calc bᵀ * F * b = bᵀ * (aᵀ * F * a) * b := by rw [hA]
      _ = (a * b)ᵀ * F * (a * b) := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = F := by rw [hab]; simp

/-- The group $O(f)$ of integral automorphs of $f(\vec{x}) = \vec{x}^{\mathsf T}F\vec{x}$ ($F$ a rational symmetric matrix): the $T \in GL_n(\mathbb Z)$ with $T^{\mathsf T}FT = F$. -/
@[kb "cassels1978" "Ch. 13, §1, p. 284 (the group O(f) of integral automorphs)"]
def autZ (F : Matrix (Fin n) (Fin n) ℚ) : Subgroup (GL (Fin n) ℤ) := (orthoQ F).comap glCast

/-- Membership in $O(f)$. -/
theorem mem_autZ {F : Matrix (Fin n) (Fin n) ℚ} {T : GL (Fin n) ℤ} :
    T ∈ autZ F ↔ (castQ T)ᵀ * F * castQ T = F := Iff.rfl

/-- For $S \in GL_n(\mathbb Q)$, the subgroup of $T \in GL_n(\mathbb Z)$ such that $S^{-1}TS$ is again in $GL_n(\mathbb Z)$: the preimage of $S\,GL_n(\mathbb Z)\,S^{-1}$. -/
def conjIntegral (S : GL (Fin n) ℚ) : Subgroup (GL (Fin n) ℤ) :=
  (glCast.range.map (MulAut.conj S).toMonoidHom).comap glCast

/-- $T \in$ `conjIntegral S` if and only if $S^{-1}TS = U$ for some $U \in GL_n(\mathbb Z)$. -/
theorem mem_conjIntegral {S : GL (Fin n) ℚ} {T : GL (Fin n) ℤ} :
    T ∈ conjIntegral S ↔ ∃ U : GL (Fin n) ℤ, glCast U = S⁻¹ * glCast T * S := by
  simp only [conjIntegral, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.mem_range,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨U, rfl⟩, hU⟩
    exact ⟨U, by rw [← hU]; group⟩
  · rintro ⟨U, hU⟩
    exact ⟨_, ⟨U, rfl⟩, by rw [hU]; group⟩


/-- First statement of Lemma 4.1: if $T \in O(f)$ and $U = S^{-1}TS$ is integral, then $U \in O(g)$ for $g(\vec{x}) = f(S\vec{x})$, i.e. $G = S^{\mathsf T}FS$. -/
theorem lemma_4_1_mem {F : Matrix (Fin n) (Fin n) ℚ} {S : GL (Fin n) ℚ} {T U : GL (Fin n) ℤ}
    (hT : T ∈ autZ F) (hU : glCast U = S⁻¹ * glCast T * S) :
    U ∈ autZ ((S : Matrix (Fin n) (Fin n) ℚ)ᵀ * F * (S : Matrix (Fin n) (Fin n) ℚ)) := by
  rw [mem_autZ] at *
  obtain ⟨s, hs⟩ : ∃ s, s = (S : Matrix (Fin n) (Fin n) ℚ) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = ((S⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) := ⟨_, rfl⟩
  have hU' : castQ (U : Matrix (Fin n) (Fin n) ℤ) = s' * castQ T * s := by
    rw [← coe_glCast, hU, Units.val_mul, Units.val_mul, coe_glCast, hs, hs']
  have hss : s * s' = 1 := by
    rw [hs, hs', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hU', ← hs]
  calc (s' * castQ T * s)ᵀ * (sᵀ * F * s) * (s' * castQ T * s)
      = sᵀ * (castQ T)ᵀ * (s * s')ᵀ * F * (s * s') * castQ T * s := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = sᵀ * ((castQ T)ᵀ * F * castQ T) * s := by
        rw [hss]; simp only [transpose_one, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hT]

/-- A rational matrix has a common denominator $d \ne 0$: $dA$ is integral. -/
theorem exists_den (A : Matrix (Fin n) (Fin n) ℚ) :
    ∃ d : ℕ, d ≠ 0 ∧ ∃ B : Matrix (Fin n) (Fin n) ℤ, castQ B = (d : ℚ) • A := by
  refine ⟨∏ i, ∏ j, (A i j).den, ?_, ?_⟩
  · simp [Finset.prod_ne_zero_iff]
  · have hdvd : ∀ i j, (A i j).den ∣ ∏ i, ∏ j, (A i j).den := fun i j =>
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).trans (Finset.dvd_prod_of_mem
        (fun i => ∏ j, (A i j).den) (Finset.mem_univ i))
    refine ⟨Matrix.of fun i j => ((∏ i, ∏ j, (A i j).den) / (A i j).den : ℕ) * (A i j).num, ?_⟩
    ext i j
    simp only [map_apply, of_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hdvd i j) (by simp)]
    have := Rat.mul_den_eq_num (A i j)
    field_simp
    rw [← this]; ring


/-- `castQ` is multiplicative. -/
theorem castQ_mul (A B : Matrix (Fin n) (Fin n) ℤ) : castQ (A * B) = castQ A * castQ B := Matrix.map_mul
/-- `castQ` is additive. -/
theorem castQ_add (A B : Matrix (Fin n) (Fin n) ℤ) : castQ (A + B) = castQ A + castQ B :=
  Matrix.map_add _ (map_add _) A B
/-- `castQ 1 = 1`. -/
theorem castQ_one : castQ (1 : Matrix (Fin n) (Fin n) ℤ) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
/-- `castQ` commutes with integer scalars. -/
theorem castQ_smul (k : ℤ) (A : Matrix (Fin n) (Fin n) ℤ) : castQ (k • A) = (k : ℚ) • castQ A := by
  ext i j; simp only [castQ, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast, Int.cast_mul]

/-- The principal congruence subgroup $\Gamma(N) = \{T \in GL_n(\mathbb Z) : T \equiv I \bmod N\}$. -/
def gamma (N : ℕ) : Subgroup (GL (Fin n) ℤ) :=
  (Units.map (RingHom.mapMatrix (Int.castRingHom (ZMod N))).toMonoidHom).ker

/-- $\Gamma(N)$ has finite index for $N \ne 0$ (kernel of reduction to the finite group $GL_n(\mathbb Z/N)$). -/
theorem gamma_finiteIndex (N : ℕ) [NeZero N] : (gamma (n := n) N).FiniteIndex := by
  unfold gamma; infer_instance

/-- An element of $\Gamma(N)$ is $I + NX$ with $X$ integral. -/
theorem eq_one_add_of_mem_gamma {N : ℕ} {T : GL (Fin n) ℤ} (hT : T ∈ gamma N) :
    ∃ X : Matrix (Fin n) (Fin n) ℤ, (T : Matrix (Fin n) (Fin n) ℤ) = 1 + (N : ℤ) • X := by
  have h : ∀ i j, (N : ℤ) ∣ (T : Matrix (Fin n) (Fin n) ℤ) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j := by
    intro i j
    have := congrArg (fun A : GL (Fin n) (ZMod N) => (A : Matrix (Fin n) (Fin n) (ZMod N)) i j)
      (MonoidHom.mem_ker.1 hT)
    change (((T : Matrix (Fin n) (Fin n) ℤ) i j : ℤ) : ZMod N) = (1 : Matrix (Fin n) (Fin n) (ZMod N)) i j at this
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, this]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  refine ⟨Matrix.of fun i j => ((T : Matrix (Fin n) (Fin n) ℤ) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) / N, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
  rw [Int.mul_ediv_cancel' (h i j)]; ring

/-- Proof of Lemma 4.1: $S^{-1}TS$ is integral whenever $T \equiv I \bmod s_1s_2$, where $s_1S^{-1}$ and $s_2S$ are integral. -/
theorem gamma_le_conjIntegral (S : GL (Fin n) ℚ) : ∃ N : ℕ, N ≠ 0 ∧ gamma N ≤ conjIntegral S := by
  obtain ⟨d₁, hd₁, B₁, hB₁⟩ := exists_den ((S⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)
  obtain ⟨d₂, hd₂, B₂, hB₂⟩ := exists_den (S : Matrix (Fin n) (Fin n) ℚ)
  refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, fun T hT => ?_⟩
  obtain ⟨X, hX⟩ := eq_one_add_of_mem_gamma hT
  rw [mem_conjIntegral]
  obtain ⟨s, hs⟩ : ∃ s, s = (S : Matrix (Fin n) (Fin n) ℚ) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = ((S⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) := ⟨_, rfl⟩
  have hss : s' * s = 1 := by rw [hs, hs', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set V : Matrix (Fin n) (Fin n) ℤ := 1 + B₁ * X * B₂
  have hV : castQ V = s' * castQ T * s := by
    rw [castQ_add, castQ_one, castQ_mul, castQ_mul, hB₁, hB₂, hX, castQ_add, castQ_one, castQ_smul,
      ← hs, ← hs']
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_assoc, hss]
    congr 2; push_cast; ring
  have hdetQ : ∀ A : Matrix (Fin n) (Fin n) ℤ, (castQ A).det = (A.det : ℚ) := fun A =>
    (RingHom.map_det (Int.castRingHom ℚ) A).symm
  have hdet : V.det = (T : Matrix (Fin n) (Fin n) ℤ).det := by
    have h1 : (castQ V).det = (castQ (T : Matrix (Fin n) (Fin n) ℤ)).det := by
      rw [hV, det_mul, det_mul, mul_comm (det s') _, mul_assoc, ← det_mul s' s, hss, det_one, mul_one]
    rw [hdetQ, hdetQ] at h1
    exact_mod_cast h1
  have hu : IsUnit V.det := by
    rw [hdet, ← GeneralLinearGroup.val_det_apply]; exact (GeneralLinearGroup.det T).isUnit
  refine ⟨Matrix.nonsingInvUnit V hu, Units.ext ?_⟩
  rw [coe_glCast, Units.val_mul, Units.val_mul, coe_glCast, ← hs, ← hs']
  exact hV


/-- The $T$ with $S^{-1}TS$ integral form a subgroup of finite index in any subgroup $K$ of $GL_n(\mathbb Z)$. -/
theorem relIndex_conjIntegral_ne_zero (S : GL (Fin n) ℚ) (K : Subgroup (GL (Fin n) ℤ)) :
    (conjIntegral S).relIndex K ≠ 0 := by
  obtain ⟨N, hN, hle⟩ := gamma_le_conjIntegral S
  have : NeZero N := ⟨hN⟩
  have := gamma_finiteIndex (n := n) N
  have : (gamma (n := n) N).IsFiniteRelIndex ⊤ := Subgroup.isFiniteRelIndex_top_iff.2 this
  have : (gamma (n := n) N).IsFiniteRelIndex K := Subgroup.isFiniteRelIndex_of_le_right _ le_top
  have : (conjIntegral S).IsFiniteRelIndex K := Subgroup.isFiniteRelIndex_of_le_left K hle
  exact Subgroup.relIndex_ne_zero

/-- **Lemma 4.1**: let $g(\vec{x}) = f(S\vec{x})$ with $S$ a nonsingular rational matrix ($G = S^{\mathsf T}FS$). (i) If $T \in O(f)$ and $U = S^{-1}TS$ is integral then $U \in O(g)$; (ii) the $T \in O(f)$ with $S^{-1}TS$ integral form a subgroup of finite index of $O(f)$; (iii) the $U \in O(g)$ with $SUS^{-1}$ integral (exactly the $U$ arising in (i)) form a subgroup of finite index of $O(g)$. Finite index is expressed as nonzero relative index. -/
@[kb "cassels1978" "Ch. 13, §4, Lemma 4.1, p. 300"]
theorem lemma_4_1 (F : Matrix (Fin n) (Fin n) ℚ) (S : GL (Fin n) ℚ) :
    (∀ T ∈ autZ F, ∀ U : GL (Fin n) ℤ, glCast U = S⁻¹ * glCast T * S →
      U ∈ autZ ((S : Matrix (Fin n) (Fin n) ℚ)ᵀ * F * (S : Matrix (Fin n) (Fin n) ℚ))) ∧
    (conjIntegral S).relIndex (autZ F) ≠ 0 ∧
    (conjIntegral S⁻¹).relIndex (autZ ((S : Matrix (Fin n) (Fin n) ℚ)ᵀ * F * (S : Matrix (Fin n) (Fin n) ℚ))) ≠ 0 :=
  ⟨fun _ hT _ hU => lemma_4_1_mem hT hU, relIndex_conjIntegral_ne_zero _ _, relIndex_conjIntegral_ne_zero _ _⟩

end QuadFormsKB.Cassels.Ch13
