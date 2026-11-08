/-
# O'Meara §106F, toward 106.r38: the listed lattices as integral forms

**Layer:** as in `Sec106Rank13Basis.lean` and `Sec106Rank13Forms.lean`. For $m = 8, 12$ and the basis data `e8Data`,
`e12Data`, the lattice $E_m \perp \mathbb Z^k$ = `omearaEPerp m (m + k)` has the Gram form
`ofMatrixZ (sumI G k)` ($G$ = `CartanMatrix.E 8`, resp. `d12Gram`). Indices are 0-based.

**Proves** (all unconditional)
* `gram_blk`: the Gram identity in the form used by the bridge lemmas;
* `det_gram_eq_one_of_unimodular`: the Gram matrix of a basis of a unimodular lattice on $I_n$ has determinant $1$;
* `posDefGram_sumI_G`, `det_sumI_G`: the Gram matrices of $E_m \perp \mathbb Z^k$ are positive definite of determinant
  $1$;
* `no_norm_one_e8`, `no_norm_one_d12`: $E_8$ and $E_{12}$ have no vector of norm $1$;
* `card_aut_d12_le`: $|\mathrm{Aut}(E_{12})| \le 2^{11}\cdot 12!$ for the integral form of $E_{12}$ (from
  `card_autLat_omearaE_twelve_le`).
-/
import QuadFormsKB.Literature.OMeara.Sec106Rank13Basis
import QuadFormsKB.Literature.OMeara.Sec106Rank13Bridge
import QuadFormsKB.Literature.OMeara.Sec106Rank13Forms
import QuadFormsKB.Literature.OMeara.Sec106Rank13AutE12
import QuadFormsKB.Literature.Cassels.Ch10.Thm71Coords

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Siegel LocalDensity ConwaySloane.Mass QuadFormsKB.Tamagawa.Frames

variable {n : ℕ}

/-- **The Gram matrix of a basis of a unimodular lattice has determinant $1$.** If $G \in M_n(\mathbb Z)$ is the Gram
matrix $B^{\mathsf T}B$ of $B \in \mathrm{GL}_n(\mathbb Q)$ and $B\mathbb Z^n$ is unimodular on $I_n$, then $\det G = 1$. -/
theorem det_gram_eq_one_of_unimodular (B : GL (Fin n) ℚ) (G : Matrix (Fin n) (Fin n) ℤ)
    (hG : G.map (Int.castRingHom ℚ) = B.valᵀ * B.val)
    (hU : IsUnimodularZ (sumSqForm n) (glImage B intVec)) : G.det = 1 := by
  set Gq : Matrix (Fin n) (Fin n) ℚ := B.valᵀ * B.val with hGq
  have hBu : IsUnit B.val.det := (Matrix.isUnit_iff_isUnit_det _).mp B.isUnit
  have hGu : IsUnit Gq.det := by rw [hGq, det_mul, det_transpose]; exact hBu.mul hBu
  -- the columns of `Gq⁻¹` are integral
  have hcol : ∀ i j, ∃ z : ℤ, Gq⁻¹ i j = z := by
    intro i j
    set c : Fin n → ℚ := Gq⁻¹ *ᵥ Pi.single j 1 with hc
    have hGc : Gq *ᵥ c = Pi.single j 1 := by
      rw [hc, mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, one_mulVec]
    have hmem : B.val *ᵥ c ∈ glImage B intVec := by
      rw [← hU]
      intro y hy
      obtain ⟨w, hw, rfl⟩ := mem_glImage.mp hy
      choose z hz using mem_intVec_iff_int.mp hw
      refine ⟨z j, ?_⟩
      rw [DefiniteForms.bil_sumSq]
      have e : (B.val *ᵥ c) ⬝ᵥ (B.val *ᵥ w) = (Gq *ᵥ c) ⬝ᵥ w := by
        rw [hGq, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
      rw [e, hGc, single_one_dotProduct, hz j]
      ring
    obtain ⟨w, hw, hwc⟩ := mem_glImage.mp hmem
    have hwc' : w = c := by
      have := congrArg (fun v => (B⁻¹).val *ᵥ v) hwc
      simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at this
      exact this
    obtain ⟨z, hz⟩ := mem_intVec_iff_int.mp hw i
    refine ⟨z, ?_⟩
    rw [← hz, hwc', hc]
    simp [mulVec, dotProduct, Pi.single_apply]
  choose N hN using hcol
  let Nm : Matrix (Fin n) (Fin n) ℤ := Matrix.of N
  have hNq : Nm.map (Int.castRingHom ℚ) = Gq⁻¹ := by ext i j; simp [Nm, hN]
  have hGN : G * Nm = 1 := by
    apply Matrix.map_injective (f := (Int.castRingHom ℚ : ℤ → ℚ)) Int.cast_injective
    show (G * Nm).map (Int.castRingHom ℚ) = (1 : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℚ)
    rw [Matrix.map_mul, hNq, hG, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.mul_nonsing_inv _ hGu
  have h := congrArg Matrix.det hGN
  rw [det_mul, det_one] at h
  have hpos : (0 : ℚ) ≤ (G.det : ℚ) := by
    have := RingHom.map_det (Int.castRingHom ℚ) G
    have e : (Int.castRingHom ℚ).mapMatrix G = Gq := hG
    rw [e, hGq, det_mul, det_transpose] at this
    have h2 : (G.det : ℚ) = B.val.det * B.val.det := by simpa using this
    rw [h2]; exact mul_self_nonneg _
  have hpos' : 0 ≤ G.det := by exact_mod_cast hpos
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h with h1 | h1
  · exact h1
  · omega

namespace EBasisData

variable {m : ℕ} (D : EBasisData m)

/-- **The Gram identity**: $\sum_i ((B \oplus 1)x)_i^2 = (G \oplus I_k)(x)$. -/
theorem gram_blk (k : ℕ) (x : Fin (m + k) → ℚ) :
    (sumSq (m + k)).evalIn ℚ ((D.blk k).val *ᵥ x) = (ofMatrixZ (sumI D.G k)).evalIn ℚ x := by
  rw [evalIn_sumSq, Cassels.Thm71Coords.evalIn_ofMatrixZ _ (sumI_symm D.G_symm)]
  have h := D.blk_norm k x
  simp only [dotProduct, sq] at h ⊢
  rw [h]
  rfl

/-- The Gram matrix of $E_m \perp \mathbb Z^k$ in the block basis is $B^{\mathsf T}B$. -/
theorem sumI_map (k : ℕ) : (sumI D.G k).map (Int.castRingHom ℚ) = (D.blk k).valᵀ * (D.blk k).val :=
  (D.blk_gram k).symm

/-- The Gram matrix $G \oplus I_k$ is positive definite. -/
theorem posDefGram_sumI (k : ℕ) : PosDefGram (sumI D.G k) := by
  refine ⟨sumI_symm D.G_symm, fun x hx => ?_⟩
  have e : x ⬝ᵥ (gramQ (sumI D.G k) *ᵥ x) = ((D.blk k).val *ᵥ x) ⬝ᵥ ((D.blk k).val *ᵥ x) := by
    rw [gramQ, D.sumI_map, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
      Matrix.transpose_transpose]
  rw [e]
  have hne : (D.blk k).val *ᵥ x ≠ 0 := by
    intro h
    apply hx
    have := congrArg (fun v => ((D.blk k)⁻¹).val *ᵥ v) h
    simpa [mulVec_mulVec, ← Units.val_mul] using this
  exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    (Ne.symm fun h => hne (dotProduct_self_eq_zero.mp h))

/-- The Gram matrix $G \oplus I_k$ has determinant $1$ ($4 \mid m$, $m \ge 8$). -/
theorem det_sumI (h4 : 4 ∣ m) (h8 : 8 ≤ m) (k : ℕ) : (sumI D.G k).det = 1 := by
  refine det_gram_eq_one_of_unimodular (D.blk k) _ (D.sumI_map k) ?_
  rw [D.glImage_blk h4 (by omega) k]
  exact isUnimodularZ_omearaEPerp h4 h8 k

end EBasisData

/-- **Automorphisms of a Gram form are automorphisms of the lattice.** If $B$ is a basis with Gram form $R$ (`hB`), then
$g \mapsto BgB^{-1}$ embeds $\mathrm{Aut}(R)$ into $O(B\mathbb Z^n)$; and $O(B\mathbb Z^n)$ is finite when $R$ is positive
definite (`hR`), so $|\mathrm{Aut}(R)| \le |O(B\mathbb Z^n)|$. -/
theorem card_aut_le_card_autLat {R : QuadForm ℤ n} (hR : IntQF.PosDef R) (B : GL (Fin n) ℚ)
    (hB : ∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (B.val *ᵥ x) = R.evalIn ℚ x) :
    Nat.card (Aut R) ≤ Nat.card (autLat (sumSqForm n) (glImage B intVec)) := by
  classical
  have hRH := hessian_map_eq_of_gram B.val hB
  let cast : GL (Fin n) ℤ →* GL (Fin n) ℚ := Units.map (Int.castRingHom ℚ).mapMatrix.toMonoidHom
  have hcast : ∀ g : GL (Fin n) ℤ, (cast g).val = g.val.map (Int.castRingHom ℚ) := fun _ => rfl
  -- conjugation preserves the form
  have horth : ∀ g ∈ Aut R, B * cast g * B⁻¹ ∈ orthGroup (sumSqForm n) ℚ := by
    intro g hg
    have hH := (Siegel.eval_mulVec_eq_iff_hessian R R g.val).mp hg
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M.map (algebraMap ℤ ℚ)) hH
    simp only [Matrix.map_mul, Matrix.transpose_map] at h1
    rw [hRH] at h1
    have hk : (B * cast g).valᵀ * (B * cast g).val = B.valᵀ * B.val := by
      have h2 : (2 : ℚ) • ((B * cast g).valᵀ * (B * cast g).val) = (2 : ℚ) • (B.valᵀ * B.val) := by
        rw [← h1, Units.val_mul, transpose_mul, hcast]
        simp only [algebraMap_int_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      exact smul_right_injective _ (two_ne_zero (α := ℚ)) h2
    apply mem_orthGroup_sumSqForm
    have h1 : B.val * (B⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (B * cast g * B⁻¹).valᵀ * (B * cast g * B⁻¹).val
        = (B⁻¹).valᵀ * ((B * cast g).valᵀ * (B * cast g).val) * (B⁻¹).val := by
          rw [Units.val_mul (B * cast g), transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (B.val * (B⁻¹).val)ᵀ * (B.val * (B⁻¹).val) := by
          rw [hk, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, transpose_one, Matrix.one_mul]
  have hcZ : ∀ g : GL (Fin n) ℤ, glImage (cast g) intVec = intVec := by
    intro g
    ext x
    rw [mem_glImage]
    have hz : ∀ (M : GL (Fin n) ℤ) (z : Fin n → ℤ),
        M.val.map (Int.castRingHom ℚ) *ᵥ (fun i => (z i : ℚ)) = fun i => ((M.val *ᵥ z) i : ℚ) := by
      intro M z; funext i; simp [Matrix.mulVec, dotProduct]
    constructor
    · rintro ⟨y, hy, rfl⟩
      choose z hz' using mem_intVec_iff_int.mp hy
      rw [show y = fun i => (z i : ℚ) from funext hz', hcast, hz, mem_intVec_iff_int]
      exact fun i => ⟨_, rfl⟩
    · intro hx
      choose z hz' using mem_intVec_iff_int.mp hx
      refine ⟨fun i => (((g⁻¹ : GL (Fin n) ℤ).val *ᵥ z) i : ℚ), mem_intVec_iff_int.mpr fun i => ⟨_, rfl⟩, ?_⟩
      rw [hcast, hz, mulVec_mulVec, Units.mul_inv, one_mulVec]
      exact (funext hz').symm
  let Φ : Aut R → autLat (sumSqForm n) (glImage B intVec) := fun g =>
    ⟨⟨B * cast g.1 * B⁻¹, horth g.1 g.2⟩, by
      change glImage (B * cast g.1 * B⁻¹) (glImage B intVec) = glImage B intVec
      rw [← glImage_mul, mul_assoc, inv_mul_cancel, mul_one, glImage_mul, hcZ]⟩
  have hΦ : Function.Injective Φ := by
    intro g h hgh
    have e : B * cast g.1 * B⁻¹ = B * cast h.1 * B⁻¹ := congrArg Subtype.val (congrArg Subtype.val hgh)
    have e2 : cast g.1 = cast h.1 := by simpa using e
    apply Subtype.ext
    apply Units.ext
    have e3 := congrArg Units.val e2
    rw [hcast, hcast] at e3
    exact Matrix.map_injective (f := (Int.castRingHom ℚ : ℤ → ℚ)) Int.cast_injective e3
  -- finiteness of the lattice automorphisms, via the inverse conjugation
  have : Finite (Aut R) := IntQF.PosDef.finite_aut hR
  have hfin : Finite (autLat (sumSqForm n) (glImage B intVec)) := by
    have hex : ∀ σ : autLat (sumSqForm n) (glImage B intVec),
        ∃ A : GL (Fin n) ℤ, A.val.map (Int.castRingHom ℚ) = (B⁻¹ * (σ : GL (Fin n) ℚ) * B).val := by
      intro σ
      refine exists_glZ_of_glImage_intVec _ ?_
      have hσ : glImage ((σ : orthGroup (sumSqForm n) ℚ) : GL (Fin n) ℚ) (glImage B intVec) = glImage B intVec :=
        σ.2
      rw [glImage_mul, glImage_mul, hσ, ← glImage_mul, inv_mul_cancel, glImage_one]
    choose Ψ hΨ using hex
    have hΨR : ∀ σ, Ψ σ ∈ Aut R := by
      intro σ
      have hσ := (σ : orthGroup (sumSqForm n) ℚ).2
      intro x
      apply Int.cast_injective (α := ℚ)
      rw [← evalIn_intCast, ← evalIn_intCast, ← hB, ← hB]
      have hv : (fun i => (((Ψ σ).val *ᵥ x) i : ℚ)) = (B⁻¹ * (σ : GL (Fin n) ℚ) * B).val *ᵥ fun i => (x i : ℚ) := by
        rw [← hΨ σ]; funext i; simp [Matrix.mulVec, dotProduct]
      have hBB : ∀ v : Fin n → ℚ, B.val *ᵥ ((B⁻¹).val *ᵥ v) = v := fun v => by
        rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      rw [hv, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hBB, evalIn_sumSq_eq_sumSqForm,
        evalIn_sumSq_eq_sumSqForm, evalIn_mulVec_of_mem (sumSqForm n) hσ]
    refine Finite.of_injective (fun σ => (⟨Ψ σ, hΨR σ⟩ : Aut R)) ?_
    intro σ τ hστ
    have e := congrArg (fun A : Aut R => (A.1.val.map (Int.castRingHom ℚ))) hστ
    simp only [hΨ] at e
    have e2 : B⁻¹ * (σ : GL (Fin n) ℚ) * B = B⁻¹ * (τ : GL (Fin n) ℚ) * B := Units.ext e
    have e3 : (σ : GL (Fin n) ℚ) = (τ : GL (Fin n) ℚ) := by simpa using e2
    exact Subtype.ext (Subtype.ext e3)
  exact Nat.card_le_card_of_injective Φ hΦ

end QuadFormsKB.Lattices
