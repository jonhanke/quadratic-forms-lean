/-
# The local identity for frames at every finite prime, for an arbitrary adapted frame

**Layer:** the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ of a number field at a finite prime (dyadic included).

For $Q_0$ over $\mathcal O_F$ of rank $N = r + n'$, a frame type $T_0$ of rank $r$ and an adapted frame $Q_0\circ g = T_0\perp Q'$
(`AdaptedFrameT`), the lattice $\Lambda = g_\mathfrak p^{-1}\mathfrak o_\mathfrak p^N$ lives in the split space $V_\mathfrak p = (F_\mathfrak p^N, T\perp Q')$.
This file proves the **local identity at $\Lambda$** (the frame version of `orbitalLocalIdentityAt_of_law`):
$$W_\mathfrak p(\Lambda)\,\beta_\mathfrak p(Q_0,Q_0)\,|\det H_{T_0}|_\mathfrak p^{\,n'} = \beta_\mathfrak p(Q',Q')\,\beta_\mathfrak p(Q_0,T_0)\,|\det g|_\mathfrak p^{\,n'+1},$$
$W_\mathfrak p(\Lambda)$ = `locFrameTypeSumG` (Weil 1982, §3.4 and §4.5 [unverified]). For $g = 1$ it is the
`frameLocalIdentity`; for $r = 1$ it is
the identity for vectors ($|\det g|^{n+1}$ with $n' + 1 = n$).

**Proof.** The local types at $\Lambda$ are the $O(Q')(F_\mathfrak p)$-orbits of lattices $h\Lambda$ ($h\in O(T\perp Q')(F_\mathfrak p)$) containing the standard
frame $E$. In the coordinates of $Q_0$ (via $g_\mathfrak p$) such a lattice contains the integral frame $y = g_\mathfrak p h^{-1}E$ of $T$;
* `locWeightG_eq_relRatio` : the weight of the type is the index ratio of $K(G\mathfrak o^N)\cap\mathrm{St}(GE)$ and $K(\mathfrak o^N)\cap\mathrm{St}(GE)$
  ($G = g_\mathfrak p h^{-1}\mathrm{diag}(1_r,\varpi^b 1_{n'})$; the stabilizer of $E$ in $O(T\perp Q')$ is $\mathrm{diag}(1, O(Q'))$);
* `locWeightG_frame` : the per-frame identity (`perF`) turns it into the near count of the $K$-orbit of $y$;
* `frameLocalIdentityGen_of_law` : the $K$-orbits of the $y_t$ partition the solutions of $Q_0\circ X\equiv T$ (disjointness by openness of orbits,
  `exists_frame_openMat`; cover by Witt's theorem; Hensel for frames, `card_sol_eq_sum_gNear`), so the weighted sum is the local density $\beta(Q_0,T_0)$.

The $\alpha$ transformation law is proved at every prime (`alphaLaw_global`), so `frameLocalIdentityGen` is unconditional. No assumption $n' \ge 3$
(or $n' \ge 1$) is used.

Sources: Weil 1982, §3.4 and §4.5 [unverified]. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FramePerY
import QuadFormsKB.Tamagawa.FrameGlobalGen
import QuadFormsKB.Tamagawa.FrameAdapted
import QuadFormsKB.Tamagawa.LocalSmith

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.Tamagawa Lattices NumberField IsDedekindDomain

/-! ### The groups: $O(Q')$ inside $O(T\perp Q')$ inside $\mathrm{GL}_N$ -/

section Groups

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T : QuadForm F r)
  (Q' : QuadForm F n')

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $O(Q')(F_\mathfrak p) \to \mathrm{GL}_{r+n'}(F_\mathfrak p)$, $a \mapsto \mathrm{diag}(1_r, a)$. -/
def embB : orthGroup Q' Fv →* GL (Fin (r + n')) Fv :=
  (orthGroup (blockForm T Q') Fv).subtype.comp (orthEmbB T Q' Fv)

theorem embB_injective : Function.Injective (embB v T Q') :=
  (orthGroup (blockForm T Q') Fv).subtype_injective.comp (orthEmbB_injective T Q' Fv)

theorem embB_apply (a : orthGroup Q' Fv) : embB v T Q' a = blockGLB (r := r) (a : GL (Fin n') Fv) := rfl

theorem embB_val (a : orthGroup Q' Fv) :
    (embB v T Q' a).val = blockMat 1 0 0 (a : GL (Fin n') Fv).val := rfl

theorem embB_mul_stdFrameMat (a : orthGroup Q' Fv) :
    (embB v T Q' a).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) = stdFrameMat :=
  orthEmbB_mul_stdFrameMat T Q' Fv a

theorem exists_embB_eq (hT : (T.hessian.map (algebraMap F Fv)).det ≠ 0) {g : GL (Fin (r + n')) Fv}
    (hg : ((blockForm T Q').map (algebraMap F Fv)).compMat g.val = (blockForm T Q').map (algebraMap F Fv))
    (hge : g.val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) = stdFrameMat) : ∃ a, embB v T Q' a = g := by
  have hgO : g ∈ orthGroup (blockForm T Q') Fv := (mem_orthGroup_iff_compMat v _ g).mpr hg
  obtain ⟨a, ha⟩ := exists_orthEmbB_eq T Q' Fv hT ⟨g, hgO⟩ hge
  exact ⟨a, by rw [embB, MonoidHom.comp_apply, ha]; rfl⟩

/-- $\varpi^b\cdot 1_{n'}$ as an element of $\mathrm{GL}_{n'}(F_\mathfrak p)$. -/
def sclGL (b : ℕ) : GL (Fin n') Fv :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (((NF.π v : 𝔬) : Fv) ^ b • (1 : Matrix (Fin n') (Fin n') Fv)) (by
    rw [det_smul, det_one, mul_one]
    exact pow_ne_zero _ (pow_ne_zero _ (fun h => (NF.irreducible_π v).ne_zero
      (Subtype.ext (by simpa using h)))))

/-- $D = \mathrm{diag}(1_r, \varpi^b 1_{n'})$. -/
def dMatB (b : ℕ) : GL (Fin (r + n')) Fv := blockGLB (r := r) (sclGL v (n' := n') b)

theorem dMatB_val (b : ℕ) :
    (dMatB v (r := r) (n' := n') b).val =
      blockMat 1 0 0 (((NF.π v : 𝔬) : Fv) ^ b • (1 : Matrix (Fin n') (Fin n') Fv)) := rfl

theorem dMatB_comm (b : ℕ) (a : GL (Fin n') Fv) :
    dMatB v (r := r) b * blockGLB (r := r) a = blockGLB (r := r) a * dMatB v b := by
  rw [dMatB, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  show (((NF.π v : 𝔬) : Fv) ^ b • (1 : Matrix (Fin n') (Fin n') Fv)) * a.val =
    a.val * (((NF.π v : 𝔬) : Fv) ^ b • (1 : Matrix (Fin n') (Fin n') Fv))
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem dMatB_mul_stdFrameMat (b : ℕ) :
    (dMatB v (r := r) (n' := n') b).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) = stdFrameMat :=
  blockMat_one_mul_stdFrameMat _

theorem det_dMatB (b : ℕ) :
    (dMatB v (r := r) (n' := n') b).val.det = (((NF.π v : 𝔬) : Fv) ^ b) ^ n' := by
  rw [dMatB_val, det_blockMat_diag, det_one, one_mul, det_smul, det_one, mul_one, Fintype.card_fin]

/-- **The stabilizer of a local type** maps onto $K(M)\cap\mathrm{St}(E)$. -/
theorem map_stabilizer_eq (hT : (T.hessian.map (algebraMap F Fv)).det ≠ 0)
    {Λ : Submodule 𝔬 (Fin (r + n') → Fv)} (M : LocFrameSetG v T Q' Λ) :
    (stabilizer (orthGroup Q' Fv) M).map (embB v T Q') =
      KL v ((blockForm T Q').map (algebraMap F Fv)) M.1 ⊓ stabF v (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_KL, mem_stabF]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨(mem_orthGroup_iff_compMat v _ _).mp (orthEmbB T Q' Fv a).2, congrArg Subtype.val ha⟩,
      embB_mul_stdFrameMat v T Q' a⟩
  · rintro ⟨⟨hgQ, hgM⟩, hge⟩
    obtain ⟨a, rfl⟩ := exists_embB_eq v T Q' hT hgQ hge
    exact ⟨a, Subtype.ext hgM, rfl⟩

/-- **The reference stabilizer** $\mathrm{diag}(1, O(\mathfrak o_\mathfrak p^{n'}))$ is $K(D\,\mathfrak o_\mathfrak p^{N})\cap\mathrm{St}(E)$. -/
theorem map_stdStab_eq (hT : (T.hessian.map (algebraMap F Fv)).det ≠ 0) (b : ℕ) :
    (stdStab Q' v).map (embB v T Q') =
      KL v ((blockForm T Q').map (algebraMap F Fv)) (locAct v (dMatB v b) (std v)) ⊓
        stabF v (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) := by
  have key : ∀ a : GL (Fin n') Fv, locAct v (blockGLB (r := r) a) (locAct v (dMatB v b) (std v)) =
      locAct v (dMatB v b) (std v) ↔ locAct v a (std v) = std v := by
    intro a
    rw [← locAct_mul, ← dMatB_comm, locAct_mul, ← locAct_blockGLB_std_iff (r := r)]
    constructor
    · intro h
      have := congrArg (locAct v (dMatB v b)⁻¹) h
      rwa [locAct_inv_locAct, locAct_inv_locAct] at this
    · intro h; rw [h]
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_KL, mem_stabF]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨(mem_orthGroup_iff_compMat v _ _).mp (orthEmbB T Q' Fv a).2, ?_⟩,
      embB_mul_stdFrameMat v T Q' a⟩
    rw [embB_apply, key]; exact ha
  · rintro ⟨⟨hgQ, hgD⟩, hge⟩
    obtain ⟨a, rfl⟩ := exists_embB_eq v T Q' hT hgQ hge
    refine ⟨a, ?_, rfl⟩
    rw [embB_apply, key] at hgD
    exact hgD

end Groups

/-! ### The adapted frame in local coordinates and the weights of the local types -/

section Weights

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F))
  (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r)
  (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "TF" => T₀.map (algebraMap (𝓞 F) F)
local notation "QF'" => fr.Q'.map (algebraMap (𝓞 F) F)
local notation "QB" => blockForm TF QF'
local notation "gv" => Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g
local notation "Qov" => QuadForm.map (algebraMap 𝔬 Fv) (NF.Qp v Q₀)

/-- **The frame over $F_\mathfrak p$**: $Q_0\circ g = T\perp Q'$ with the integral model of $Q_0$. -/
theorem frameG_local : (Qov).compMat (gv).val = (QB).map (algebraMap F Fv) := by
  rw [map_Qp_eq, ← fr.compMat_eq, ← map_compMat]
  rfl

/-- **The weight of a local type as an index ratio of frame stabilizers** in the coordinates of $Q_0$: for $M = h\Lambda$
($\Lambda = g_\mathfrak p^{-1}\mathfrak o^N$, $h \in O(T\perp Q')(F_\mathfrak p)$) and $G = g_\mathfrak p h^{-1}\mathrm{diag}(1_r,\varpi^b 1_{n'})$. -/
theorem locWeightG_eq_relRatio (hT : T₀.Nondegenerate)
    (M : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))) (h : orthGroup QB Fv)
    (hM : locAct v (h : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v)) = M.1) (b : ℕ) (G : GL (Fin (r + n')) Fv)
    (hG : G = gv * (h : GL (Fin (r + n')) Fv)⁻¹ * dMatB v b) :
    locFrameWeightG v TF QF' (locAct v gv⁻¹ (std v)) M =
      relRatio (KL v (Qov) (locAct v G (std v)) ⊓
          stabF v (G.val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)))
        (KL v (Qov) (std v) ⊓ stabF v (G.val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv))) := by
  have hTF := fl_hess_ne_v v T₀ hT
  set hv : GL (Fin (r + n')) Fv := (h : GL (Fin (r + n')) Fv)
  set ĝ := gv * hv⁻¹
  have hframe := frameG_local v Q₀ T₀ fr
  have hhO : hv⁻¹ ∈ orthGroup QB Fv := by
    rw [← Subgroup.coe_inv]; exact (h⁻¹).2
  have hĝ : (Qov).compMat ĝ.val = (QB).map (algebraMap F Fv) := by
    rw [Units.val_mul, ← compMat_mul, hframe]
    exact (mem_orthGroup_iff_compMat v _ _).mp hhO
  have hinj : Function.Injective (MulAut.conj ĝ).toMonoidHom := (MulAut.conj ĝ).injective
  have hKL : ∀ Λ' : Submodule 𝔬 (Fin (r + n') → Fv),
      (KL v ((QB).map (algebraMap F Fv)) Λ').map (MulAut.conj ĝ).toMonoidHom = KL v (Qov) (locAct v ĝ Λ') := by
    intro Λ'; rw [KL_locAct, hĝ]
  have hΛ : locAct v ĝ M.1 = std v := by
    rw [← hM, ← locAct_mul, ← locAct_mul]
    show locAct v (gv * hv⁻¹ * hv * gv⁻¹) (std v) = std v
    rw [inv_mul_cancel_right, mul_inv_cancel, locAct_one]
  have hD : ĝ.val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) =
      G.val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) := by
    rw [hG, Units.val_mul ĝ (dMatB v b), Matrix.mul_assoc, dMatB_mul_stdFrameMat]
  show relRatio (stdStab _ v) (stabilizer _ M) = _
  rw [← relRatio_map (embB_injective v TF QF'), map_stdStab_eq v TF QF' hTF b, map_stabilizer_eq v TF QF' hTF M,
    ← relRatio_map hinj, Subgroup.map_inf_eq _ _ _ hinj, Subgroup.map_inf_eq _ _ _ hinj, hKL, hKL]
  have hs : (stabF v (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)).map (MulAut.conj ĝ).toMonoidHom =
      stabF v (G.val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)) := by
    rw [stabF_map_conj, hD]
  have hl : locAct v ĝ (locAct v (dMatB v b) (std v)) = locAct v G (std v) := by
    rw [← locAct_mul, hG]
  rw [hs, hl, hΛ]

theorem mul_blockMat_one_castAdd {A : Type*} [CommRing A] (X : Matrix (Fin (r + n')) (Fin (r + n')) A)
    (D' : Matrix (Fin n') (Fin n') A) (i : Fin (r + n')) (j : Fin r) :
    (X * (blockMat 1 0 0 D' : Matrix (Fin (r + n')) (Fin (r + n')) A)) i (Fin.castAdd n' j) =
      X i (Fin.castAdd n' j) := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  simp [Matrix.one_apply]

theorem mul_blockMat_one_natAdd {A : Type*} [CommRing A] (X : Matrix (Fin (r + n')) (Fin (r + n')) A) (c : A)
    (i : Fin (r + n')) (l : Fin n') :
    (X * (blockMat 1 0 0 (c • (1 : Matrix (Fin n') (Fin n') A)) : Matrix (Fin (r + n')) (Fin (r + n')) A)) i
        (Fin.natAdd r l) = X i (Fin.natAdd r l) * c := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  simp [Matrix.one_apply, Matrix.smul_apply]

theorem mul_stdFrameMat_apply {A : Type*} [CommRing A] (X : Matrix (Fin (r + n')) (Fin (r + n')) A) (i : Fin (r + n'))
    (j : Fin r) : (X * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) A)) i j = X i (Fin.castAdd n' j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd n' j)]
  · simp [stdFrameMat]
  · intro l _ hl
    simp [stdFrameMat, hl]
  · simp

theorem frameMat_mulVec_stdFrame {A : Type*} [CommRing A] (P : Matrix (Fin (r + n')) (Fin (r + n')) A)
    (i : Fin (r + n')) (j : Fin r) :
    (frameMat r P *ᵥ (stdFrame : Fin (r + n') × Fin r → A)) (i, j) = P i (Fin.castAdd n' j) := by
  rw [frameMat_mulVec]
  show ∑ l, P i l * stdFrame (l, j) = _
  rw [Finset.sum_eq_single (Fin.castAdd n' j)]
  · simp [stdFrame, stdFrameMat]
  · intro l _ hl
    simp [stdFrame, stdFrameMat, hl]
  · simp

/-- $Q'$ is nondegenerate if $Q_0$ is (since $Q_0\circ g = T\perp Q'$). -/
theorem adapted_nondegenerate (hQ₀ : Q₀.Nondegenerate) : fr.Q'.Nondegenerate := by
  have h1 : (blockForm TF QF').hessian.det ≠ 0 := by
    rw [← fr.compMat_eq, hessian_compMat, det_mul, det_mul, det_transpose]
    have hg : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    exact mul_ne_zero (mul_ne_zero hg (fl_hess_ne Q₀ hQ₀)) hg
  rw [det_hessian_blockForm] at h1
  have h2 := right_ne_zero_of_mul h1
  rw [lid_hessian_map_alg, ← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero_iff _ RingOfIntegers.coe_injective]
    at h2
  exact h2

/-- **The weight of a local type, by the per-frame identity** (any prime where `AlphaLawAt` holds): for a type $M = h\Lambda$
with $y = g_\mathfrak p h^{-1}E \in \mathfrak o_\mathfrak p^{N\times r}$ (the integral frame of $T$ in the coordinates of $Q_0$) and $\pi^d\,\Vert\,\det H_T$,
for all large $s$ and $k$:
$$w(M)\,\beta(Q_0)\,q^{kD} = N_{k,s}(Ky)\,\|\det g\|^{n'+1}\,q^{dn'}\,\beta(Q').$$
*Proof:* the split sublattice $g_\mathfrak p h^{-1}(\mathfrak o^r\oplus\varpi^b\mathfrak o^{n'})$ ($b$ large), `locWeightG_eq_relRatio` and `perF`; the scaling
$\beta(\varpi^{2b}Q') = q^{bn'(n'+1)}\beta(Q')$ cancels $\|\varpi^b\|^{n'(n'+1)}$. -/
theorem locWeightG_frame (hQ₀ : Q₀.Nondegenerate) (hT : T₀.Nondegenerate)
    (hlaw : ∀ (P : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) (hP : P.det ≠ 0), AlphaLawAt v (NF.Qp v Q₀) P hP)
    {Pd : Matrix (Fin r) (Fin r) 𝔬} (hPd : Pd.det ≠ 0) {dg : Fin r → 𝔬}
    (hPdg : (NF.Qp v T₀).compMat Pd = QuadForm.diag dg) (hdg : ∀ i, dg i ≠ 0) {d : ℕ}
    (hd : NF.π v ^ d ∣ (NF.Qp v T₀).hessian.det) (hd' : ¬ NF.π v ^ (d + 1) ∣ (NF.Qp v T₀).hessian.det)
    (M : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))) (h : orthGroup QB Fv)
    (hM : locAct v (h : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v)) = M.1) (yo : Fin (r + n') × Fin r → 𝔬)
    (hy : coeFrame v yo = (gv).val * ((h⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ᶠ k in Filter.atTop,
      locFrameWeightG v TF QF' (locAct v gv⁻¹ (std v)) M * localDensityForm (NF.Qp v Q₀) (NF.Qp v Q₀) (NF.π v) *
          (q 𝔬 : ℝ) ^ (k * ((r + n') * r - r * (r + 1) / 2)) =
        gNear (formF (NF.Qp v Q₀)) (tc (NF.Qp v T₀)) (NF.π v) k s
            (gOrbit ((frameHom r 𝔬).comp (repStd v (Qov))) ⊤ yo) *
          ‖algebraMap F Fv fr.g.val.det‖ ^ (n' + 1) * (q 𝔬 : ℝ) ^ (d * n') *
          localDensityForm (NF.Qp v fr.Q') (NF.Qp v fr.Q') (NF.π v) := by
  classical
  have hπ := NF.irreducible_π v
  set Qo := NF.Qp v Q₀
  set Q'o := NF.Qp v fr.Q'
  set hv : GL (Fin (r + n')) Fv := (h : GL (Fin (r + n')) Fv)
  set ĝ := gv * hv⁻¹
  have hQo : Qo.Nondegenerate := NF.nondegenerate_Qp v hQ₀
  have hQ'₀ : fr.Q'.Nondegenerate := adapted_nondegenerate Q₀ T₀ fr hQ₀
  have hQ'o : Q'o.Nondegenerate := NF.nondegenerate_Qp v hQ'₀
  have hframe := frameG_local v Q₀ T₀ fr
  have hhO : hv⁻¹ ∈ orthGroup QB Fv := by
    rw [← Subgroup.coe_inv]; exact (h⁻¹).2
  have hĝ : (Qov).compMat ĝ.val = (QB).map (algebraMap F Fv) := by
    rw [Units.val_mul, ← compMat_mul, hframe]
    exact (mem_orthGroup_iff_compMat v _ _).mp hhO
  -- the integral matrix of the split sublattice
  obtain ⟨b, A, hA⟩ := exists_scale_integral v ĝ.val
  set ϖ : Fv := ((NF.π v : 𝔬) : Fv)
  set D := dMatB v (r := r) (n' := n') b
  set P : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬 :=
    Matrix.of fun i k => Fin.addCases (motive := fun _ => 𝔬) (fun j => yo (i, j)) (fun l => A i (Fin.natAdd r l)) k
  have hyc : ∀ i j, (yo (i, j) : Fv) = ĝ.val i (Fin.castAdd n' j) := by
    intro i j
    have e : ((h⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) = hv⁻¹ := Subgroup.coe_inv _ h
    show coeFrame v yo i j = _
    rw [hy, e]
    exact mul_stdFrameMat_apply ((gv).val * hv⁻¹.val) i j
  have hPmap : P.map (algebraMap 𝔬 Fv) = (ĝ * D).val := by
    refine Matrix.ext fun i k => ?_
    rw [Units.val_mul, dMatB_val]
    induction k using Fin.addCases with
    | left j =>
      rw [mul_blockMat_one_castAdd, ← hyc]
      simp [P]
    | right l =>
      rw [mul_blockMat_one_natAdd]
      have := congrFun (congrFun hA i) (Fin.natAdd r l)
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
      simp only [P, Matrix.map_apply, Matrix.of_apply, Fin.addCases_right]
      rw [this, mul_comm]
  have hPdet : P.det ≠ 0 := by
    intro h0
    have : (P.map (algebraMap 𝔬 Fv)).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    rw [hPmap] at this
    exact ((ĝ * D).isUnit.map Matrix.detMonoidHom).ne_zero this
  have hglP : glOf v P hPdet = ĝ * D := Units.ext (by rw [glOf_val, hPmap])
  have hPe : frameMat r P *ᵥ (stdFrame : Fin (r + n') × Fin r → 𝔬) = yo := by
    funext ⟨i, j⟩
    rw [frameMat_mulVec_stdFrame]
    simp [P]
  -- the split form of the sublattice
  have hQ''nd : (((NF.π v) ^ b) ^ 2 • Q'o).Nondegenerate :=
    nondegenerate_smul hQ'o (pow_ne_zero _ (pow_ne_zero _ hπ.ne_zero))
  have hsplit : Qo.compMat P = blockForm (NF.Qp v T₀) (((NF.π v) ^ b) ^ 2 • Q'o) := by
    apply quadForm_map_o_inj v
    rw [← map_compMat, hPmap, Units.val_mul, ← compMat_mul, hĝ, dMatB_val, map_blockForm, map_blockForm,
      compMat_blockMat_diag, compMat_one, compMat_smul_one, QuadFormsKB.Tamagawa.map_smul_form,
      ← fl_map_Qp v T₀, ← fl_map_Qp v fr.Q']
    simp [map_pow]
  obtain ⟨s₀, hs₀⟩ := perF v Qo hQo (NF.Qp v T₀) _ hQ''nd hPd hPdg hdg hd hd' P hPdet hsplit (hlaw P hPdet)
  refine ⟨s₀, fun s hs => ?_⟩
  filter_upwards [hs₀ s hs] with k hk
  rw [hPe] at hk
  have hw := locWeightG_eq_relRatio v Q₀ T₀ fr hT M h hM b (glOf v P hPdet) (by rw [hglP])
  rw [hw, hk]
  -- the determinant and the scaling of `β`
  have hdetP : ‖((P.det : 𝔬) : Fv)‖ = ‖algebraMap F Fv fr.g.val.det‖ * ‖ϖ‖ ^ (b * n') := by
    have e1 : ((P.det : 𝔬) : Fv) = (ĝ * D).val.det := by
      rw [← hPmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    have hhdet : ‖hv⁻¹.val.det‖ = 1 := by
      have e : ((h⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) = hv⁻¹ := Subgroup.coe_inv _ h
      have := fw_det_pm v T₀ fr.Q' hT hQ'₀ h⁻¹
      rw [e] at this
      rcases this with h1 | h1 <;> rw [h1] <;> simp
    rw [e1, Units.val_mul, Units.val_mul, det_mul, det_mul, norm_mul, norm_mul, hhdet, mul_one, dMatB_val,
      det_blockMat_diag, det_one, one_mul, det_smul, det_one, mul_one, norm_pow, norm_pow, Fintype.card_fin,
      ← pow_mul, mul_comm b n']
    rw [show ((gv).val.det) = algebraMap F Fv fr.g.val.det by rw [RingHom.map_det]; rfl]
  have hϖ : ‖ϖ‖ = (q 𝔬 : ℝ)⁻¹ := by
    have := norm_coe_of_pow_dvd v (e := 1) (x := NF.π v) (by rw [pow_one]) (fun h' => by
      obtain ⟨u, hu⟩ := h'
      have : NF.π v * (NF.π v * u - 1) = 0 := by linear_combination -hu
      rcases mul_eq_zero.mp this with h'' | h''
      · exact hπ.ne_zero h''
      · exact hπ.not_isUnit ⟨⟨NF.π v, u, by linear_combination h'', by linear_combination h''⟩, rfl⟩)
    rw [this, pow_one]
  have h2b : NF.π v ^ (2 * b) ∣ (NF.π v ^ b) ^ 2 := by rw [← pow_mul, mul_comm]
  have h2b' : ¬ NF.π v ^ (2 * b + 1) ∣ (NF.π v ^ b) ^ 2 := by
    rw [← pow_mul, mul_comm b 2]
    intro ⟨u, hu⟩
    rw [pow_succ, mul_assoc] at hu
    have : NF.π v ^ (2 * b) * (NF.π v * u - 1) = 0 := by linear_combination -hu
    rcases mul_eq_zero.mp this with h'' | h''
    · exact pow_ne_zero _ hπ.ne_zero h''
    · exact hπ.not_isUnit ⟨⟨NF.π v, u, by linear_combination h'', by linear_combination h''⟩, rfl⟩
  rw [localDensityForm_smul Q'o hQ'o hπ h2b h2b', hdetP, hϖ]
  have hq : (0 : ℝ) < q 𝔬 := Nat.cast_pos.mpr q_pos
  have hT2 : 2 * b * (n' * (n' + 1) / 2) = b * n' * (n' + 1) := by
    obtain ⟨t', ht'⟩ := (Nat.even_mul_succ_self n').two_dvd
    rw [ht', Nat.mul_div_cancel_left t' two_pos, mul_assoc b n', ht']; ring
  rw [hT2]
  have hX : ((q 𝔬 : ℝ)⁻¹ ^ (b * n')) ^ (n' + 1) * (q 𝔬 : ℝ) ^ (b * n' * (n' + 1)) = 1 := by
    rw [← pow_mul, inv_pow, inv_mul_cancel₀ (pow_pos hq _).ne']
  rw [mul_pow]
  linear_combination (gNear (formF Qo) (tc (NF.Qp v T₀)) (NF.π v) k s
      (gOrbit ((frameHom r 𝔬).comp (repStd v (Qov))) ⊤ yo) *
    ‖algebraMap F Fv fr.g.val.det‖ ^ (n' + 1) * (q 𝔬 : ℝ) ^ (d * n') *
    localDensityForm Q'o Q'o (NF.π v) : ℝ) * hX

/-! ### Frames and lattices: the data of a local type, and the correspondence of orbits -/

theorem gcancel (g : GL (Fin (r + n')) Fv) (X : Matrix (Fin (r + n')) (Fin r) Fv) :
    g.val * (g⁻¹.val * X) = X := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem gcancel' (g : GL (Fin (r + n')) Fv) (X : Matrix (Fin (r + n')) (Fin r) Fv) :
    g⁻¹.val * (g.val * X) = X := by
  rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- **Data of a local type:** every $M \in Y_\mathfrak p(\Lambda)$ is $h\Lambda$ with $h \in O(T\perp Q')(F_\mathfrak p)$, and $y = g_\mathfrak p h^{-1}E$ is an
integral frame of $T_0$ in the coordinates of $Q_0$. -/
theorem frameType_data (M : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))) :
    ∃ (h : orthGroup QB Fv) (yo : Fin (r + n') × Fin r → 𝔬),
      locAct v (h : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v)) = M.1 ∧
      coeFrame v yo = (gv).val * ((h : GL (Fin (r + n')) Fv)⁻¹).val *
        (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) ∧
      formF (NF.Qp v Q₀) yo = tc (NF.Qp v T₀) := by
  obtain ⟨h, hh⟩ := M.2.1
  have hcol : ∀ j, ∃ c : Fin (r + n') → 𝔬, (fun i => (c i : Fv)) =
      (gv).val *ᵥ (((h : GL (Fin (r + n')) Fv)⁻¹).val *ᵥ stdCol v (n' := n') j) := by
    intro j
    have hm : stdCol v (n' := n') j ∈ locAct v (h : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v)) := hh ▸ M.2.2 j
    obtain ⟨y, hy, hgy0⟩ := hm
    have hgy : (h : GL (Fin (r + n')) Fv).val *ᵥ y = stdCol v (n' := n') j := hgy0
    have hy' : ((h : GL (Fin (r + n')) Fv)⁻¹).val *ᵥ stdCol v (n' := n') j = y := by
      rw [← hgy, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    obtain ⟨u, hu, hgu⟩ := hy
    have : (gv).val *ᵥ y = u := by rw [← hgu]; exact mulVec_inv_mulVec gv u
    rw [hy', this]
    exact integral_of_mem_std' v hu
  choose c hc using hcol
  have hgx : coeFrame v (fun p : Fin (r + n') × Fin r => c p.2 p.1) =
      (gv).val * ((h : GL (Fin (r + n')) Fv)⁻¹).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) := by
    refine Matrix.ext fun i j => ?_
    have h1 := congrFun (hc j) i
    rw [mulVec_mulVec, mulVec_stdCol] at h1
    beta_reduce at h1
    exact h1
  refine ⟨h, fun p => c p.2 p.1, hh, hgx, ?_⟩
  rw [formF_eq_tc_iff]
  refine NF.map_injective (f := algebraMap 𝔬 Fv) Subtype.val_injective ?_
  rw [← QuadForm.map_compMat]
  have hX : (toMat (fun p : Fin (r + n') × Fin r => c p.2 p.1)).map (algebraMap 𝔬 Fv) =
      coeFrame v (fun p : Fin (r + n') × Fin r => c p.2 p.1) := rfl
  have hhO : ((h : GL (Fin (r + n')) Fv)⁻¹) ∈ orthGroup QB Fv := by
    rw [← Subgroup.coe_inv]; exact (h⁻¹).2
  rw [hX, hgx, ← compMat_mul, ← compMat_mul, frameG_local v Q₀ T₀ fr,
    (mem_orthGroup_iff_compMat v _ _).mp hhO, fl_frame_gram v T₀ fr.Q', fl_map_Qp v T₀]

/-- **The stabilizer of the frame lattice, in the coordinates of $Q_0$**, is $K(\mathfrak o^N)$: $g_\mathfrak p k g_\mathfrak p^{-1}\in K(\mathfrak o^N)$ iff
$k \in O(T\perp Q')(F_\mathfrak p)$ stabilizes $\Lambda = g_\mathfrak p^{-1}\mathfrak o^N$. -/
theorem conj_mem_KL_std_iff' (k : GL (Fin (r + n')) Fv) :
    gv * k * gv⁻¹ ∈ KL v (Qov) (std v) ↔
      k ∈ orthGroup QB Fv ∧ locAct v k (locAct v gv⁻¹ (std v)) = locAct v gv⁻¹ (std v) := by
  have hstd : locAct v gv (locAct v gv⁻¹ (std v)) = std v := by
    rw [← locAct_mul, mul_inv_cancel, locAct_one]
  have hKL := KL_locAct v (Qov) gv (locAct v gv⁻¹ (std v))
  rw [hstd, frameG_local v Q₀ T₀ fr] at hKL
  rw [hKL, Subgroup.mem_map_equiv (f := MulAut.conj gv), MulAut.conj_symm_apply, mem_KL,
    mem_orthGroup_iff_compMat]
  have : gv⁻¹ * (gv * k * gv⁻¹) * gv = k := by group
  rw [this]

/-- **Lattices to frames:** if $a_0 \in O(Q')(F_\mathfrak p)$ carries the lattice $h_1\Lambda$ to $h_2\Lambda$, then the frame $y_2 = g_\mathfrak p h_2^{-1}E$
lies in the $K$-orbit of $y_1 = g_\mathfrak p h_1^{-1}E$. -/
theorem orbit_of_lattice (h₁ h₂ : orthGroup QB Fv) (a₀ : orthGroup QF' Fv)
    (ha : locAct v (embB v TF QF' a₀) (locAct v (h₁ : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v))) =
      locAct v (h₂ : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v)))
    (y₁ y₂ : Fin (r + n') × Fin r → 𝔬)
    (hy₁ : coeFrame v y₁ = (gv).val * ((h₁ : GL (Fin (r + n')) Fv)⁻¹).val *
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv))
    (hy₂ : coeFrame v y₂ = (gv).val * ((h₂ : GL (Fin (r + n')) Fv)⁻¹).val *
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)) :
    y₂ ∈ gOrbit ((frameHom r 𝔬).comp (repStd v (Qov))) ⊤ y₁ := by
  set k : orthGroup QB Fv := h₂⁻¹ * orthEmbB TF QF' Fv a₀ * h₁ with hkdef
  have hk : locAct v (k : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v)) = locAct v gv⁻¹ (std v) := by
    simp only [hkdef, Subgroup.coe_mul, Subgroup.coe_inv, locAct_mul]
    change locAct v (h₂ : GL (Fin (r + n')) Fv)⁻¹ (locAct v (embB v TF QF' a₀)
      (locAct v (h₁ : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v)))) = _
    rw [ha, locAct_inv_locAct]
  have hκ : gv * (k : GL (Fin (r + n')) Fv) * gv⁻¹ ∈ KL v (Qov) (std v) :=
    (conj_mem_KL_std_iff' v Q₀ T₀ fr _).mpr ⟨k.2, hk⟩
  refine ⟨⟨_, hκ⟩, Subgroup.mem_top _, ?_⟩
  apply pf_coeFrame_injective v
  show coeFrame v (frameMat r (repStd v (Qov) ⟨_, hκ⟩) *ᵥ y₁) = coeFrame v y₂
  rw [pf_coeFrame_frameMat, repStd_map, hy₁, hy₂]
  show (gv * (k : GL (Fin (r + n')) Fv) * gv⁻¹).val * ((gv).val * ((h₁ : GL (Fin (r + n')) Fv)⁻¹).val *
    stdFrameMat) = (gv).val * ((h₂ : GL (Fin (r + n')) Fv)⁻¹).val * stdFrameMat
  have hE := embB_mul_stdFrameMat v TF QF' a₀
  simp only [hkdef, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.mul_assoc, gcancel, gcancel']
  have hE' : ((orthEmbB TF QF' Fv a₀ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) = stdFrameMat := hE
  rw [hE']

/-- **Frames to lattices:** if $\kappa \in K(\mathfrak o^N)$ carries $y_1 = g_\mathfrak p h_1^{-1}E$ to $y_2 = g_\mathfrak p h_2^{-1}E$, then some
$a_0 \in O(Q')(F_\mathfrak p)$ carries $h_1\Lambda$ to $h_2\Lambda$ (the stabilizer of $E$ in $O(T\perp Q')$ is $O(Q')$, `exists_embB_eq`). -/
theorem lattice_of_orbit (hT : T₀.Nondegenerate) (h₁ h₂ : orthGroup QB Fv) (y₁ y₂ : Fin (r + n') × Fin r → 𝔬)
    (hy₁ : coeFrame v y₁ = (gv).val * ((h₁ : GL (Fin (r + n')) Fv)⁻¹).val *
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv))
    (hy₂ : coeFrame v y₂ = (gv).val * ((h₂ : GL (Fin (r + n')) Fv)⁻¹).val *
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv))
    (κ : KL v (Qov) (std v)) (hκ : frameMat r (repStd v (Qov) κ) *ᵥ y₁ = y₂) :
    ∃ a₀ : orthGroup QF' Fv, locAct v (embB v TF QF' a₀)
      (locAct v (h₁ : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v))) =
      locAct v (h₂ : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v)) := by
  have hTF := fl_hess_ne_v v T₀ hT
  set k₀ : GL (Fin (r + n')) Fv := gv⁻¹ * (κ : GL (Fin (r + n')) Fv) * gv with hk₀def
  have hk₀ : gv * k₀ * gv⁻¹ = (κ : GL (Fin (r + n')) Fv) := by simp only [hk₀def]; group
  have hk₀mem := (conj_mem_KL_std_iff' v Q₀ T₀ fr k₀).mp (by rw [hk₀]; exact κ.2)
  have hY := congrArg (coeFrame v) hκ
  rw [pf_coeFrame_frameMat, repStd_map, hy₁, hy₂] at hY
  rw [Matrix.mul_assoc, Matrix.mul_assoc] at hY
  have key : k₀.val * (((h₁ : GL (Fin (r + n')) Fv)⁻¹).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)) =
      ((h₂ : GL (Fin (r + n')) Fv)⁻¹).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) := by
    calc k₀.val * (((h₁ : GL (Fin (r + n')) Fv)⁻¹).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv))
        = gv⁻¹.val * ((κ : GL (Fin (r + n')) Fv).val * ((gv).val *
            (((h₁ : GL (Fin (r + n')) Fv)⁻¹).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)))) := by
          simp only [hk₀def, Units.val_mul, Matrix.mul_assoc]
      _ = gv⁻¹.val * ((gv).val * (((h₂ : GL (Fin (r + n')) Fv)⁻¹).val *
            (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv))) := by rw [hY]
      _ = _ := gcancel' v _ _
  set γ : orthGroup QB Fv := h₂ * ⟨k₀, hk₀mem.1⟩ * h₁⁻¹ with hγdef
  have hγE : (γ : GL (Fin (r + n')) Fv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) = stdFrameMat := by
    simp only [hγdef, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.mul_assoc]
    rw [key, gcancel v]
  obtain ⟨a₀, ha₀⟩ := exists_embB_eq v TF QF' hTF ((mem_orthGroup_iff_compMat v _ _).mp γ.2) hγE
  refine ⟨a₀, ?_⟩
  rw [ha₀]
  simp only [hγdef, Subgroup.coe_mul, Subgroup.coe_inv, locAct_mul]
  rw [locAct_inv_locAct, hk₀mem.2]

/-! ### The local identity -/

/-- **The local identity for frames at an arbitrary lattice, from the $\alpha$ law** (Weil 1982, §3.4 and §4.5 [unverified]).
Given the $\alpha$ transformation law for $Q_0\otimes\mathfrak o_\mathfrak p$ (`AlphaLawAt`, every $P$),
$$W_\mathfrak p(\Lambda)\,\beta_\mathfrak p(Q_0,Q_0)\,|\det H_{T_0}|_\mathfrak p^{\,n'} = \beta_\mathfrak p(Q',Q')\,\beta_\mathfrak p(Q_0,T_0)\,|\det g|_\mathfrak p^{\,n'+1},
\qquad \Lambda = g_\mathfrak p^{-1}\mathfrak o_\mathfrak p^{r+n'}.$$ -/
theorem frameLocalIdentityGen_of_law (hQ₀ : Q₀.Nondegenerate) (hT : T₀.Nondegenerate)
    (hlaw : ∀ (P : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) (hP : P.det ≠ 0), AlphaLawAt v (NF.Qp v Q₀) P hP) :
    locFrameTypeSumG v TF QF' (locAct v gv⁻¹ (std v)) * NF.localDensityForm v Q₀ Q₀ *
        ‖algebraMap F Fv (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ n' =
      NF.localDensityForm v fr.Q' fr.Q' * NF.localDensityForm v Q₀ T₀ * ‖algebraMap F Fv fr.g.val.det‖ ^ (n' + 1) := by
  classical
  have hπ := NF.irreducible_π v
  set Qo := NF.Qp v Q₀ with hQodef
  set To := NF.Qp v T₀ with hTodef
  set Q'o := NF.Qp v fr.Q' with hQ'odef
  have hQo : Qo.Nondegenerate := NF.nondegenerate_Qp v hQ₀
  have hTo : To.Nondegenerate := NF.nondegenerate_Qp v hT
  have hQ'₀ : fr.Q'.Nondegenerate := adapted_nondegenerate Q₀ T₀ fr hQ₀
  have hTF := fl_hess_ne_v v T₀ hT
  have h2 : (2 : 𝔬) ≠ 0 := NF.two_ne_zero' v
  have h4 : (4 : 𝔬) ≠ 0 := by
    rw [show (4 : 𝔬) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  obtain ⟨Pd, dg, hPdet, hdg, hP⟩ := lid_exists_diag_local v T₀ hT
  choose fi hfi hfi' using fun i => DVR.exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h4 (hdg i))
  set f := Finset.univ.sup fi with hfdef
  have hf : ∀ i, ¬ NF.π v ^ (f + 1) ∣ 4 * dg i := fun i hh =>
    hfi' i ((pow_dvd_pow _ (by have := Finset.le_sup (f := fi) (Finset.mem_univ i); omega)).trans hh)
  obtain ⟨d, hd, hd'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ hTo
  -- the data of the local types
  choose hτ yo hτM hτy hτQ using fun t : LocFrameTypesG v TF QF' (locAct v gv⁻¹ (std v)) =>
    frameType_data v Q₀ T₀ fr (locFrameRepG v TF QF' (locAct v gv⁻¹ (std v)) t)
  have hρ : ∀ (κ : KL v (Qov) (std v)) (z : Fin (r + n') × Fin r → 𝔬),
      ((frameHom r 𝔬).comp (repStd v (Qov))) κ *ᵥ z = frameMat r (repStd v (Qov) κ) *ᵥ z := fun _ _ => rfl
  have hxa : ∀ (κ : KL v (Qov) (std v)) (z : Fin (r + n') × Fin r → 𝔬), formF Qo z = tc To →
      formF Qo (frameMat r (repStd v (Qov) κ) *ᵥ z) = tc To := by
    intro κ z hz
    rw [formF_frameMat_of_compMat _ (compMat_repStd v rfl κ), hz]
  -- disjointness of the orbits of the types
  have hdisjAll : ∀ s, r * f + 1 ≤ s → ∀ t t', ∀ a ∈ gOrbit ((frameHom r 𝔬).comp (repStd v (Qov))) ⊤ (yo t),
      ∀ a' ∈ gOrbit ((frameHom r 𝔬).comp (repStd v (Qov))) ⊤ (yo t'), (∀ i, NF.π v ^ s ∣ a i - a' i) → t = t' := by
    rintro s hs t t' a ⟨κ, -, ha⟩ a' ⟨κ', -, ha'⟩ haa'
    have hQa : formF Qo a = tc To := by rw [← ha, hρ]; exact hxa κ _ (hτQ t)
    have hQa' : formF Qo a' = tc To := by rw [← ha', hρ]; exact hxa κ' _ (hτQ t')
    obtain ⟨M₀, hM₀, hM₀a, -⟩ := exists_frame_openMat hπ Qo To hPdet hP hdg hf hs hQa hQa'
      (fun i => by rw [← dvd_neg, neg_sub]; exact haa' i)
    obtain ⟨τT, hτT⟩ := exists_repStd_eq v rfl hQo M₀ hM₀
    set κ₀ := κ'⁻¹ * τT * κ with hκ₀def
    have hκ₀ : frameMat r (repStd v (Qov) κ₀) *ᵥ yo t = yo t' := by
      have hτ' : ((frameHom r 𝔬).comp (repStd v (Qov))) τT *ᵥ a = a' := by
        rw [hρ, hτT]; exact hM₀a
      show ((frameHom r 𝔬).comp (repStd v (Qov))) κ₀ *ᵥ yo t = yo t'
      rw [hκ₀def, map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, ha, hτ', ← ha']
      exact mulVec_inv_mulVec_g ((frameHom r 𝔬).comp (repStd v (Qov))) κ' _
    obtain ⟨a₀, ha₀⟩ := lattice_of_orbit v Q₀ T₀ fr hT (hτ t) (hτ t') (yo t) (yo t') (hτy t) (hτy t') κ₀ hκ₀
    have hmem : locFrameRepG v TF QF' (locAct v gv⁻¹ (std v)) t' ∈
        orbit (orthGroup QF' Fv) (locFrameRepG v TF QF' (locAct v gv⁻¹ (std v)) t) := by
      refine ⟨a₀, Subtype.ext ?_⟩
      rw [LocFrameSetG.smul_val, ← hτM t, ← hτM t']
      exact ha₀
    have := Quotient.sound' (s₁ := orbitRel _ _) hmem
    rw [locFrameRepG_mk, locFrameRepG_mk] at this
    exact this.symm
  have hfin : Finite (LocFrameTypesG v TF QF' (locAct v gv⁻¹ (std v))) := by
    have := DVR.finite_vec (ι := Fin (r + n') × Fin r) (NF.π v) hπ (r * f + 1)
    refine Finite.of_injective (fun t => DVR.redI (NF.π v) (r * f + 1) (yo t)) fun t t' htt => ?_
    exact hdisjAll (r * f + 1) le_rfl t t' (yo t) ⟨1, Subgroup.mem_top 1, by simp⟩ (yo t')
      ⟨1, Subgroup.mem_top 1, by simp⟩ ((DVR.redI_eq_iff _ _ _ _).mp htt)
  let _ : Fintype (LocFrameTypesG v TF QF' (locAct v gv⁻¹ (std v))) := Fintype.ofFinite _
  -- every solution lies in the orbit of some type
  have hQF : ((QB).hessian.map (algebraMap F Fv)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_hessian_blockForm]
    exact (map_ne_zero _).mpr (mul_ne_zero (fl_hess_ne T₀ hT) (fl_hess_ne fr.Q' hQ'₀))
  have hcover : ∀ y, formF Qo y = tc To →
      ∃ t, y ∈ gOrbit ((frameHom r 𝔬).comp (repStd v (Qov))) ⊤ (yo t) := by
    intro y hy
    set X : Matrix (Fin (r + n')) (Fin r) Fv := gv⁻¹.val * coeFrame v y with hXdef
    have hX : ((QB).map (algebraMap F Fv)).compMat X = (TF).map (algebraMap F Fv) := by
      rw [← frameG_local v Q₀ T₀ fr, compMat_mul, hXdef, gcancel v]
      have e : (toMat y).map (algebraMap 𝔬 Fv) = coeFrame v y := rfl
      rw [← e, map_compMat, (formF_eq_tc_iff _ _ _).mp hy]
      exact (fl_map_Qp v T₀).symm
    obtain ⟨γ, hγ⟩ := exists_orthGroup_mul_stdFrameMat TF QF' Fv hQF hTF hX
    have hXj : ∀ j, (γ : GL (Fin (r + n')) Fv).val *ᵥ stdCol v (n' := n') j =
        gv⁻¹.val *ᵥ (fun i => (y (i, j) : Fv)) := by
      intro j
      rw [mulVec_stdCol, hγ]
      funext i
      simp [hXdef, Matrix.mul_apply, Matrix.mulVec, dotProduct, coeFrame]
    let M' : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v)) :=
      ⟨locAct v ((γ⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v)), ⟨γ⁻¹, rfl⟩, fun j => by
        refine ⟨gv⁻¹.val *ᵥ (fun i => (y (i, j) : Fv)), ⟨_, coe_mem_std' v _, rfl⟩, ?_⟩
        show ((γ⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *ᵥ (gv⁻¹.val *ᵥ (fun i => (y (i, j) : Fv))) =
          stdCol v (n' := n') j
        rw [← hXj j, Subgroup.coe_inv, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]⟩
    set t : LocFrameTypesG v TF QF' (locAct v gv⁻¹ (std v)) := Quotient.mk'' M' with htdef
    obtain ⟨a, ha⟩ : M' ∈ orbit (orthGroup QF' Fv) (locFrameRepG v TF QF' (locAct v gv⁻¹ (std v)) t) :=
      Quotient.exact' (locFrameRepG_mk v TF QF' (locAct v gv⁻¹ (std v)) t).symm
    have ha1 : locAct v (embB v TF QF' a) (locAct v (hτ t : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v))) =
        locAct v ((γ⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v)) := by
      rw [hτM t]
      exact congrArg Subtype.val ha
    refine ⟨t, orbit_of_lattice v Q₀ T₀ fr (hτ t) γ⁻¹ a ha1 (yo t) y (hτy t) ?_⟩
    rw [Subgroup.coe_inv, inv_inv, Matrix.mul_assoc]
    refine Eq.trans ?_ (congrArg (fun Z => (gv).val * Z) hγ).symm
    rw [hXdef, gcancel v]
  -- the weights of the types
  choose s₀ hs₀ using fun t : LocFrameTypesG v TF QF' (locAct v gv⁻¹ (std v)) =>
    locWeightG_frame v Q₀ T₀ fr hQ₀ hT hlaw hPdet hP hdg hd hd' (locFrameRepG v TF QF' (locAct v gv⁻¹ (std v)) t)
      (hτ t) (hτM t) (yo t) (by rw [Subgroup.coe_inv]; exact hτy t)
  obtain ⟨s, hs1, hs2⟩ : ∃ s, r * f + 1 ≤ s ∧ ∀ t, s₀ t ≤ s :=
    ⟨max (r * f + 1) (Finset.univ.sup s₀), le_max_left _ _, fun t =>
      (Finset.le_sup (f := s₀) (Finset.mem_univ t)).trans (le_max_right _ _)⟩
  have hev := Filter.eventually_all.mpr fun t => hs₀ t s (hs2 t)
  obtain ⟨k, hk, hkge⟩ := (hev.and (Filter.eventually_ge_atTop (s + 2 * d + 1))).exists
  have hhensel : ∀ z : Fin (r + n') × Fin r → 𝔬, (∀ p, NF.π v ^ k ∣ formF Qo z p - tc To p) →
      ∃ y, formF Qo y = tc To ∧ ∀ i, NF.π v ^ (k - d) ∣ y i - z i :=
    fun z hz => exists_formF_eq_of_dvd hπ Qo To hd hd' (by omega) z hz
  have hpart := card_sol_eq_sum_gNear hπ (formF Qo) (tc To)
    (fun t => gOrbit ((frameHom r 𝔬).comp (repStd v (Qov))) ⊤ (yo t)) hcover (hdisjAll s hs1) (k := k) (e := d)
    (by omega) hhensel
  have hrepN : DVR.repCountForm Qo To (NF.π v) k = ∑ t, gNear (formF Qo) (tc To) (NF.π v) k s
      (gOrbit ((frameHom r 𝔬).comp (repStd v (Qov))) ⊤ (yo t)) := by
    rw [DVR.repCountForm_eq_card_sol]; exact hpart
  set G : ℝ := ‖algebraMap F Fv fr.g.val.det‖ ^ (n' + 1) with hG
  have hq : (0 : ℝ) < (q 𝔬 : ℝ) := Nat.cast_pos.mpr q_pos
  set Wd : ℝ := (q 𝔬 : ℝ) ^ (d * n') with hWd
  set B' : ℝ := localDensityForm Q'o Q'o (NF.π v) with hB'
  set B : ℝ := localDensityForm Qo Qo (NF.π v) with hB
  set Qk : ℝ := (q 𝔬 : ℝ) ^ (k * ((r + n') * r - r * (r + 1) / 2)) with hQk
  have hmain : locFrameTypeSumG v TF QF' (locAct v gv⁻¹ (std v)) * B * Qk =
      (DVR.repCountForm Qo To (NF.π v) k : ℝ) * (G * Wd * B') := by
    unfold locFrameTypeSumG
    rw [finsum_eq_sum_of_fintype, Finset.sum_mul, Finset.sum_mul, hrepN, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hk t]; ring
  have hβ1 : NF.localDensityForm v Q₀ T₀ = (DVR.repCountForm Qo To (NF.π v) k : ℝ) / Qk := by
    rw [NF.localDensityForm_eq_completion]
    exact DVR.localDensityForm_eq _ _ _ hπ d hd hd' (Nat.le_add_right r n') k (by omega)
  have hnorm : ‖algebraMap F Fv (algebraMap (𝓞 F) F T₀.hessian.det)‖ = ((q 𝔬 : ℝ) ^ d)⁻¹ := by
    have := lid_norm_coe_of_pow_dvd v (x := (NF.Qp v T₀).hessian.det) hd hd'
    rw [NF.det_hessian_Qp] at this
    exact this
  have hα : NF.localDensityForm v Q₀ Q₀ = B := NF.localDensityForm_eq_completion v Q₀ Q₀
  have hα' : NF.localDensityForm v fr.Q' fr.Q' = B' := NF.localDensityForm_eq_completion v fr.Q' fr.Q'
  have hQk0 : Qk ≠ 0 := (pow_pos hq _).ne'
  have hX2 : Wd * ((q 𝔬 : ℝ) ^ d)⁻¹ ^ n' = 1 := by
    rw [hWd, inv_pow, ← pow_mul, mul_inv_cancel₀ (pow_pos hq _).ne']
  rw [hβ1, hnorm, hα, hα']
  set W := locFrameTypeSumG v TF QF' (locAct v gv⁻¹ (std v))
  set RC : ℝ := (DVR.repCountForm Qo To (NF.π v) k : ℝ)
  have hWB : W * B = RC * (G * Wd * B') / Qk := by
    rw [eq_div_iff hQk0]; exact hmain
  calc W * B * ((q 𝔬 : ℝ) ^ d)⁻¹ ^ n' = RC * (G * Wd * B') / Qk * ((q 𝔬 : ℝ) ^ d)⁻¹ ^ n' := by rw [hWB]
    _ = B' * (RC / Qk) * G * (Wd * ((q 𝔬 : ℝ) ^ d)⁻¹ ^ n') := by ring
    _ = B' * (RC / Qk) * G := by rw [hX2, mul_one]

end Weights

/-- **The local identity for frames at every finite prime, for an arbitrary adapted frame** (Weil 1982, §3.4 and §4.5 [unverified]).
For $Q_0$, $T_0$ nondegenerate over $\mathcal O_F$ of ranks $r + n'$ and $r$ and an adapted frame $Q_0\circ g = T_0\perp Q'$,
at every finite prime $\mathfrak p$ (dyadic included), with $\Lambda = g_\mathfrak p^{-1}\mathfrak o_\mathfrak p^{r+n'}$,
$$W_\mathfrak p(\Lambda)\,\beta_\mathfrak p(Q_0,Q_0)\,|\det H_{T_0}|_\mathfrak p^{\,n'} = \beta_\mathfrak p(Q',Q')\,\beta_\mathfrak p(Q_0,T_0)\,|\det g|_\mathfrak p^{\,n'+1}.$$
Unconditional (the $\alpha$ law is `alphaLaw_global`); no hypothesis on $n'$. For $g = 1$ this is `frameLocalIdentity`. -/
@[kb "weil1982" "§3.4 and §4.5 (local identity for frames at every prime) [unverified]"]
theorem frameLocalIdentityGen {F : Type} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F))
    (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ₀ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F))) :
    locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
        (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) *
        NF.localDensityForm v Q₀ Q₀ * ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ n' =
      NF.localDensityForm v fr.Q' fr.Q' * NF.localDensityForm v Q₀ T₀ *
        ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n' + 1) :=
  frameLocalIdentityGen_of_law v Q₀ T₀ fr hQ₀ hT fun P hP => alphaLaw_global v Q₀ hQ₀ P hP

end QuadFormsKB.Tamagawa.Frames
