/-
# Shimura 2004, Proposition 4.6: the shape (4.15) of $\Theta(a)$ for $a \in P'_2$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, §4.5,
Proposition 4.6, (4.15), (4.18)–(4.21) (printed pp. 31–32). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `Wave5/Theta.lean`: $V$ with a hyperbolic pair $e_1, f_1$, $U = (Fe_1 +
Ff_1)^\perp$ (`uSpace Q e₁ f₁`), a hyperbolic pair $e_2, f_2$ in $U$, $X = (Fe_2 + Ff_2)^\perp \cap U$, and
$\Theta : A(V) \cong M_4(A(X))$ (`thetaBig`), rows and columns indexed by $(i, k) \in \{0,1\}^2$ in the order
$(0,0), (0,1), (1,0), (1,1)$, i.e. Shimura's indices $1, 2, 3, 4$. $I_2 = Fe_1 + Fe_2$ (`I₂`), and
$P'_2 = \{a \in G'(V) \mid I_2\tau(a) = I_2\}$ is `parabolicG' Q I₂` ((4.8a)).

**Proves** (all unconditional; standard axioms only):
* $\Theta(e_1)$ and $\Theta(e_2)$ explicitly (`thetaBig_e₁`, `thetaBig_e₂`);
* **Proposition 4.6, (4.15)**: for $a \in P'_2$ the first column of $\Theta(a)$ vanishes below the diagonal and the
  last row vanishes to the left of the diagonal (`prop_4_6_shape`);
* **(4.21)**: if $ae_1a^{-1} = se_1 + re_2$ and $ae_2a^{-1} = qe_1 + pe_2$ (Shimura's (4.18), (4.19)), then
  $a_1 = (ps - qr)d_4$ for the corner entries $a_1 = \Theta(a)_{11}$, $d_4 = \Theta(a)_{44}$ (`formula_4_21`);
  the numbers $r, s, p, q$ exist for every $a \in P'_2$ (`exists_conj_coeffs`), and $ps - qr$ is the determinant
  of the matrix of $y \mapsto aya^{-1}$ on $I_2$.

*Not formalized here* (recorded as a loose end): the homomorphism $\pi : P_2^+ \to GL_2(F)$ of (4.16) as a map, the
statement $a_1, d_4 \in G^+(X)$, and (4.17) $a_1d_4^* = \nu(a) = \det(\pi(a))\nu(d_4)$. (In our copy of the book the
display (4.16) is not legible; Shimura's proof uses only that $\det\pi(a) = ps - qr$.)

The proof follows Shimura's: $\Theta(x)\Theta(a) = \Theta(a)\Theta(x\tau(a))$ and $\Theta(a)\Theta(x) =
\Theta(axa^{-1})\Theta(a)$ for $x = e_1, e_2$, compared entry by entry.
-/
import QuadFormsKB.Literature.Shimura2004.Wave5.Theta
import QuadFormsKB.Literature.Shimura2004.Wave2.Parabolic
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace Prop46

open MatrixModel Theta

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {e₁ f₁ : V} {e₂ f₂ : uSpace Q e₁ f₁}

local notation "A" => CliffordAlgebra Q

variable (e₁ e₂) in
/-- $I_2 = Fe_1 + Fe_2$ ((4.1a) with $m = 2$). -/
def I₂ : Submodule F V := Submodule.span F {e₁, (e₂ : V)}

section Hyp

variable (he₁ : Q e₁ = 0) (hf₁ : Q f₁ = 0) (hef₁ : QuadraticMap.polar Q e₁ f₁ = 1)
  (he₂ : QU Q e₁ f₁ e₂ = 0) (hf₂ : QU Q e₁ f₁ f₂ = 0) (hef₂ : QuadraticMap.polar (QU Q e₁ f₁) e₂ f₂ = 1)
include he₁ hf₁ hef₁ he₂ hf₂ hef₂

local notation "Θ" => thetaBig he₁ hf₁ hef₁ he₂ hf₂ hef₂

/-- $\Theta(e_1)$: the identity of $M_2(A(X))$ in the upper right block. -/
theorem thetaBig_e₁ :
    Θ (ι Q e₁) = Matrix.of fun p q : Fin 2 × Fin 2 => if p.1 = 0 ∧ q.1 = 1 ∧ p.2 = q.2 then 1 else 0 := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [thetaBig_apply, psi_e he₁ hf₁ hef₁]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp

/-- $\Theta(e_2) = \mathrm{diag}[\theta(e_2), -\theta(e_2)]$ with $\theta(e_2) = \begin{pmatrix} 0 & 1 \\ 0 & 0
\end{pmatrix}$. -/
theorem thetaBig_e₂ :
    Θ (ι Q (e₂ : V)) = Matrix.of fun p q : Fin 2 × Fin 2 =>
      if p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 1 then (if p.1 = 0 then 1 else -1) else 0 := by
  have h1 := psi_ι_of_mem he₁ hf₁ hef₁ e₂
  have h2 : theta he₂ hf₂ hef₂ (ι (QU Q e₁ f₁) e₂) = !![0, 1; 0, 0] := psi_e he₂ hf₂ hef₂
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [thetaBig_apply, h1]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp [h2, map_neg]

/-- $\Theta(se_1 + re_2) = s\Theta(e_1) + r\Theta(e_2)$. -/
theorem thetaBig_comb (s r : F) :
    Θ (ι Q (s • e₁ + r • (e₂ : V))) = s • Θ (ι Q e₁) + r • Θ (ι Q (e₂ : V)) := by
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]

/-- For $a \in P'_2$ and $x \in I_2$: $x\tau(a) \in I_2$, and $x = y\tau(a)$ for some $y \in I_2$. -/
theorem conj_mem (α : homogeneousCliffordGroup Q) (hα : (α : Aˣ) ∈ parabolicG' Q (I₂ e₁ e₂)) (x : V)
    (hx : x ∈ I₂ e₁ e₂) :
    (∃ y ∈ I₂ e₁ e₂, ι Q x * ((α : Aˣ) : A) = ((α : Aˣ) : A) * ι Q y) ∧
      (∃ y ∈ I₂ e₁ e₂, ((α : Aˣ) : A) * ι Q x = ι Q y * ((α : Aˣ) : A)) := by
  obtain ⟨hh, hJ⟩ := hα
  set t := tau (⟨(α : Aˣ), homogeneous_le_cliffordGroup α.2⟩ : cliffordGroup Q)
  have hspec : ∀ z : V, ι Q (t z) = (((α : Aˣ)⁻¹ : Aˣ) : A) * ι Q z * ((α : Aˣ) : A) := fun z =>
    tau_spec _ z
  constructor
  · refine ⟨t x, ?_, ?_⟩
    · have : t x ∈ (I₂ e₁ e₂).map (t : V →ₗ[F] V) := Submodule.mem_map_of_mem hx
      rwa [hJ] at this
    · rw [hspec, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  · have hx' : x ∈ (I₂ e₁ e₂).map (t : V →ₗ[F] V) := by rw [hJ]; exact hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx'
    refine ⟨y, hy, ?_⟩
    have h1 : ι Q x = (((α : Aˣ)⁻¹ : Aˣ) : A) * ι Q y * ((α : Aˣ) : A) := by
      rw [← hspec]; exact congrArg (ι Q) hyx.symm
    rw [h1, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]

omit he₁ hf₁ hef₁ he₂ hf₂ hef₂ in
theorem mem_I₂_iff (y : V) : y ∈ I₂ e₁ e₂ ↔ ∃ s r : F, y = s • e₁ + r • (e₂ : V) := by
  rw [I₂, Submodule.mem_span_pair]
  exact ⟨fun ⟨s, r, h⟩ => ⟨s, r, h.symm⟩, fun ⟨s, r, h⟩ => ⟨s, r, h.symm⟩⟩

/-- **Proposition 4.6, (4.15)** (Shimura 2004, p. 31): for $a \in P'_2$, the first column of $\Theta(a)$ is
$(a_1, 0, 0, 0)$ and its last row is $(0, 0, 0, d_4)$. -/
@[kb "shimura2004" "Prop. 4.6, (4.15), p. 31 (Θ(a) has first column (a₁, 0, 0, 0) and last row (0, 0, 0, d₄) for a ∈ P'_2)"]
theorem prop_4_6_shape (α : homogeneousCliffordGroup Q) (hα : (α : Aˣ) ∈ parabolicG' Q (I₂ e₁ e₂)) :
    (∀ x : Fin 2 × Fin 2, x ≠ (0, 0) → Θ ((α : Aˣ) : A) x (0, 0) = 0) ∧
      (∀ y : Fin 2 × Fin 2, y ≠ (1, 1) → Θ ((α : Aˣ) : A) (1, 1) y = 0) := by
  have he₁J : e₁ ∈ I₂ e₁ e₂ := Submodule.subset_span (Set.mem_insert _ _)
  have he₂J : (e₂ : V) ∈ I₂ e₁ e₂ := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  obtain ⟨⟨y₁, hy₁, H₁⟩, ⟨z₁, hz₁, K₁⟩⟩ := conj_mem he₁ hf₁ hef₁ he₂ hf₂ hef₂ α hα e₁ he₁J
  obtain ⟨⟨y₂, hy₂, H₂⟩, ⟨z₂, hz₂, K₂⟩⟩ := conj_mem he₁ hf₁ hef₁ he₂ hf₂ hef₂ α hα (e₂ : V) he₂J
  obtain ⟨s₁, r₁, rfl⟩ := (mem_I₂_iff y₁).1 hy₁
  obtain ⟨s₂, r₂, rfl⟩ := (mem_I₂_iff y₂).1 hy₂
  obtain ⟨p₁, q₁, rfl⟩ := (mem_I₂_iff z₁).1 hz₁
  obtain ⟨p₂, q₂, rfl⟩ := (mem_I₂_iff z₂).1 hz₂
  set M := Θ ((α : Aˣ) : A)
  have E₁ := congrArg Θ H₁
  have E₂ := congrArg Θ H₂
  have G₁ := congrArg Θ K₁
  have G₂ := congrArg Θ K₂
  rw [map_mul, map_mul, thetaBig_comb, thetaBig_e₁, thetaBig_e₂] at E₁ E₂ G₁ G₂
  have entry : ∀ {X Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (AU (QU Q e₁ f₁) e₂ f₂)}, X = Y →
      ∀ p q, X p q = Y p q := fun h p q => by rw [h]
  -- the entries used: first column from `E₁`, `E₂`; last row from `G₁`, `G₂`
  have c10 := entry E₁ (0, 0) (0, 0)
  have c11 := entry E₁ (0, 1) (0, 0)
  have c01 := entry E₂ (0, 0) (0, 0)
  have r10 := entry G₁ (1, 1) (1, 0)
  have r11 := entry G₁ (1, 1) (1, 1)
  have r12 := entry G₂ (1, 1) (1, 1)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, Prod.mk.injEq] at c10 c11 c01 r10 r11 r12
  simp at c10 c11 c01 r10 r11 r12
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rcases x with ⟨i, k⟩
    fin_cases i <;> fin_cases k
    · exact absurd rfl hx
    · simpa using c01
    · simpa using c10
    · simpa using c11
  · rcases y with ⟨j, l⟩
    fin_cases j <;> fin_cases l
    · simpa using r10
    · simpa using r11
    · simpa using r12
    · exact absurd rfl hy

/-- (4.18), (4.19): for $a \in P'_2$ there are $r, s, p, q \in F$ with $ae_1a^{-1} = se_1 + re_2$ and
$ae_2a^{-1} = qe_1 + pe_2$. -/
theorem exists_conj_coeffs (α : homogeneousCliffordGroup Q) (hα : (α : Aˣ) ∈ parabolicG' Q (I₂ e₁ e₂)) :
    ∃ s r q p : F, ((α : Aˣ) : A) * ι Q e₁ = ι Q (s • e₁ + r • (e₂ : V)) * ((α : Aˣ) : A) ∧
      ((α : Aˣ) : A) * ι Q (e₂ : V) = ι Q (q • e₁ + p • (e₂ : V)) * ((α : Aˣ) : A) := by
  have he₁J : e₁ ∈ I₂ e₁ e₂ := Submodule.subset_span (Set.mem_insert _ _)
  have he₂J : (e₂ : V) ∈ I₂ e₁ e₂ := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  obtain ⟨-, ⟨z₁, hz₁, K₁⟩⟩ := conj_mem he₁ hf₁ hef₁ he₂ hf₂ hef₂ α hα e₁ he₁J
  obtain ⟨-, ⟨z₂, hz₂, K₂⟩⟩ := conj_mem he₁ hf₁ hef₁ he₂ hf₂ hef₂ α hα (e₂ : V) he₂J
  obtain ⟨s, r, rfl⟩ := (mem_I₂_iff z₁).1 hz₁
  obtain ⟨q, p, rfl⟩ := (mem_I₂_iff z₂).1 hz₂
  exact ⟨s, r, q, p, K₁, K₂⟩

/-- **(4.21)** (Shimura 2004, p. 32): if $ae_1 = (se_1 + re_2)a$ and $ae_2 = (qe_1 + pe_2)a$ ((4.18), (4.19)),
then $a_1 = (ps - qr)d_4$, where $a_1 = \Theta(a)_{11}$ and $d_4 = \Theta(a)_{44}$; here $ps - qr$ is the
determinant of the matrix of $y \mapsto aya^{-1}$ on $I_2$. -/
@[kb "shimura2004" "(4.21), p. 32 (det(π(a))d₄ = (ps − qr)d₄ = a₁)"]
theorem formula_4_21 (α : homogeneousCliffordGroup Q) (hα : (α : Aˣ) ∈ parabolicG' Q (I₂ e₁ e₂)) {s r q p : F}
    (h₁ : ((α : Aˣ) : A) * ι Q e₁ = ι Q (s • e₁ + r • (e₂ : V)) * ((α : Aˣ) : A))
    (h₂ : ((α : Aˣ) : A) * ι Q (e₂ : V) = ι Q (q • e₁ + p • (e₂ : V)) * ((α : Aˣ) : A)) :
    Θ ((α : Aˣ) : A) (0, 0) (0, 0) = (p * s - q * r) • Θ ((α : Aˣ) : A) (1, 1) (1, 1) := by
  obtain ⟨hcol, hrow⟩ := prop_4_6_shape he₁ hf₁ hef₁ he₂ hf₂ hef₂ α hα
  have E₁ := congrArg Θ h₁
  have E₂ := congrArg Θ h₂
  rw [map_mul, map_mul, thetaBig_comb, thetaBig_e₁, thetaBig_e₂] at E₁ E₂
  have entry : ∀ {X Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (AU (QU Q e₁ f₁) e₂ f₂)}, X = Y →
      ∀ p q, X p q = Y p q := fun h p q => by rw [h]
  -- $a_1 = sM_{(1,0),(1,0)} + rM_{(0,1),(1,0)}$ is not needed; we use
  -- $M_{(0,1),(0,1)} = s d_4$, $M_{(1,0),(0,1)} = -r d_4$ and $a_1 = qM_{(1,0),(0,1)} + pM_{(0,1),(0,1)}$
  have k1 := entry E₁ (0, 1) (1, 1)
  have k2 := entry E₁ (1, 0) (1, 1)
  have k3 := entry E₂ (0, 0) (0, 1)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, Prod.mk.injEq] at k1 k2 k3
  simp at k1 k2 k3
  rw [k3, k1, k2, smul_neg, smul_smul, smul_smul, ← sub_eq_add_neg, ← sub_smul]

end Hyp

end Prop46

end QuadFormsKB.Shimura2004
