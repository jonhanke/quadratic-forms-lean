/-
# Weil's local orbital identity for frames, every prime

**Layer:** the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ of a number field at a finite prime $\mathfrak p$ (dyadic included).

Setting: $T_0$ of rank $r$ and $Q_0'$ of rank $n'$ over $\mathcal O_F$, nondegenerate; $Q = T\perp Q'$ (`blockForm`) on $V = F^{r+n'}$,
$L = \mathfrak o_\mathfrak p^{r+n'}$, $K = O(L)$ (`stdStab`), $H = O(Q')(F_\mathfrak p)$ acting through $\mathrm{diag}(1_r, \cdot)$ (`orthEmbB`),
$E$ the standard frame.

**Defines**
* `LocFrameSet` $= Y_\mathfrak p = \{M \in O(V)(F_\mathfrak p)\,L : E \subseteq M\}$ (the columns of $E$ lie in $M$), with the action of $H$;
* `LocFrameTypes` (the $H$-orbits), `locFrameWeight` $w(M) = [K_0' : K_M\cap K_0']/[K_M : K_M\cap K_0']$ ($K_0' = O(\mathfrak o_\mathfrak p^{n'})$),
  `locFrameTypeSum` $W_\mathfrak p = \sum_t w(M_t)$.

**Proves**
* **`frameLocalIdentity`** (Weil 1982, §3.4 [unverified]; Kitaoka 1993, §5.6 [unverified]):
  $$W_\mathfrak p\,\beta_\mathfrak p(Q, Q)\,|\det H_T|_\mathfrak p^{\,n'} = \beta_\mathfrak p(Q', Q')\,\beta_\mathfrak p(Q, T).$$
  *Proof.* For $k \gg s \gg 0$: the frames of $T$ mod $\pi^k$ are the disjoint union of the near sets of the $K$-orbits of the integral
  frames (`card_sol_eq_sum_gNear`: Hensel for frames, openness); the $K$-orbits of integral frames are the local types
  ($M = gL \mapsto Kg^{-1}E$, Witt's theorem over $F_\mathfrak p$ and the stabilizer of $E$); the orbit of $x = hE$ has
  $w(h^{-1}L)$ times as many points as that of $E$ (`frameNear_type`: orbit comparison with $J = K\cap hKh^{-1}$, invariance of near counts
  under $h$ through a basis of $L \cap h^{-1}L$, and $\Delta(h) = 1$, `modRatio_eq_one`); the orbit of $E$ has
  $|O(Q\bmod\pi^k)|/(q^{dn'}|O(Q'\bmod\pi^k)|)$ points (`frameNear_stdFrame`). The densities are these counts normalized.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameSplitCount
import QuadFormsKB.Tamagawa.LocalUnimodular

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.Tamagawa Lattices NumberField IsDedekindDomain

/-! ### Local types of frames -/

section LocalTypes

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T : QuadForm F r)
  (Q' : QuadForm F n')

local notation "QB" => blockForm T Q'
local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The $j$-th column of the standard frame, $e_j$, as a vector of $F_\mathfrak p^{r+n'}$. -/
def stdCol (j : Fin r) : Fin (r + n') → Fv := fun i => (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) i j

/-- **The local type set** $Y_\mathfrak p = \{M \in O(V)(F_\mathfrak p)\cdot\mathfrak o_\mathfrak p^{r+n'} : e_0, \dots, e_{r-1} \in M\}$ for
$V = (F^{r+n'}, T\perp Q')$ (Weil 1982, §3.4 [unverified]; Kitaoka 1993, §6.8 [unverified]). -/
@[kb "weil1982" "§3.4 (local types of frames) [unverified]"]
def LocFrameSet : Type _ :=
  {M : Submodule 𝔬 (Fin (r + n') → Fv) //
    (∃ g : orthGroup QB Fv, locAct v (g : GL (Fin (r + n')) Fv) (std v) = M) ∧ ∀ j, stdCol v (n' := n') j ∈ M}

/-- The $j$-th column of $A E$ is $A\,e_j$. -/
theorem mulVec_stdCol (A : Matrix (Fin (r + n')) (Fin (r + n')) Fv) (j : Fin r) :
    A *ᵥ stdCol v (n' := n') j = fun i => (A * stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) i j := by
  funext i; rfl

/-- Integral points of $F_\mathfrak p^N$ are the points of `std`. -/
theorem integral_of_mem_std' {N : ℕ} {y : Fin N → Fv} (hy : y ∈ std v) :
    ∃ x : Fin N → 𝔬, (fun i => (x i : Fv)) = y := by
  have hyv : ∀ i, Valued.v (y i) ≤ 1 := by
    intro i; have := hy i; rwa [neg_zero, WithZero.exp_zero] at this
  exact ⟨fun i => toO v _ (hyv i), rfl⟩

theorem coe_mem_std' {N : ℕ} (x : Fin N → 𝔬) : (fun i => (x i : Fv)) ∈ std v := by
  intro i
  rw [neg_zero, WithZero.exp_zero]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (x i).2

theorem stdCol_mem_locAct_orthEmbB (h : orthGroup Q' Fv) {M : Submodule 𝔬 (Fin (r + n') → Fv)}
    (hM : ∀ j, stdCol v (n' := n') j ∈ M) (j : Fin r) :
    stdCol v (n' := n') j ∈ locAct v (orthEmbB T Q' Fv h : GL (Fin (r + n')) Fv) M := by
  refine ⟨stdCol v (n' := n') j, hM j, ?_⟩
  have := mulVec_stdCol v (orthEmbB T Q' Fv h : GL (Fin (r + n')) Fv).val j
  rw [orthEmbB_val, blockMat_one_mul_stdFrameMat] at this
  exact this

instance LocFrameSet.instMulAction : MulAction (orthGroup Q' Fv) (LocFrameSet v T Q') where
  smul h M := ⟨locAct v (orthEmbB T Q' Fv h : GL (Fin (r + n')) Fv) M.1, by
      obtain ⟨g, hg⟩ := M.2.1
      exact ⟨orthEmbB T Q' Fv h * g, by rw [Subgroup.coe_mul, locAct_mul, hg]⟩,
    stdCol_mem_locAct_orthEmbB v T Q' h M.2.2⟩
  one_smul M := Subtype.ext (by
    show locAct v (orthEmbB T Q' Fv 1 : GL (Fin (r + n')) Fv) M.1 = M.1
    rw [map_one, OneMemClass.coe_one, locAct_one])
  mul_smul a b M := Subtype.ext (by
    show locAct v (orthEmbB T Q' Fv (a * b) : GL (Fin (r + n')) Fv) M.1 =
      locAct v (orthEmbB T Q' Fv a : GL (Fin (r + n')) Fv) (locAct v (orthEmbB T Q' Fv b : GL (Fin (r + n')) Fv) M.1)
    rw [map_mul, Subgroup.coe_mul, locAct_mul])

theorem LocFrameSet.smul_val (h : orthGroup Q' Fv) (M : LocFrameSet v T Q') :
    (h • M).1 = locAct v (orthEmbB T Q' Fv h : GL (Fin (r + n')) Fv) M.1 := rfl

theorem stdCol_mem_std (j : Fin r) : stdCol v (n' := n') j ∈ std v := by
  have : stdCol v (n' := n') j = Pi.single (Fin.castAdd n' j) (1 : Fv) := by
    funext i; simp [stdCol, stdFrameMat, Pi.single_apply]
  rw [this]; exact single_one_mem_std v _

/-- The base point $\mathfrak o_\mathfrak p^{r+n'} \in Y_\mathfrak p$. -/
def locFrameStdPt : LocFrameSet v T Q' := ⟨std v, ⟨1, locAct_one _⟩, stdCol_mem_std v⟩

/-- **The local types** at $\mathfrak p$: the $O(Q')(F_\mathfrak p)$-orbits on $Y_\mathfrak p$. -/
abbrev LocFrameTypes : Type _ := orbitRel.Quotient (orthGroup Q' Fv) (LocFrameSet v T Q')

/-- The representative of a local type: $\mathfrak o_\mathfrak p^{r+n'}$ for its own type, `Quotient.out` otherwise. -/
def locFrameRep (t : LocFrameTypes v T Q') : LocFrameSet v T Q' := by
  classical
  exact if (Quotient.mk'' (locFrameStdPt v T Q') : LocFrameTypes v T Q') = t then locFrameStdPt v T Q' else t.out

theorem locFrameRep_mk (t : LocFrameTypes v T Q') :
    (Quotient.mk'' (locFrameRep v T Q' t) : LocFrameTypes v T Q') = t := by
  classical
  unfold locFrameRep
  split_ifs with h
  · exact h
  · exact Quotient.out_eq' t

theorem locFrameRep_std : locFrameRep v T Q' (Quotient.mk'' (locFrameStdPt v T Q')) = locFrameStdPt v T Q' := by
  classical
  unfold locFrameRep
  rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]

/-- **The local weight** of $M \in Y_\mathfrak p$: with $K_M = \mathrm{Stab}_{O(Q')(F_\mathfrak p)}(M)$ and $K_0' = O(\mathfrak o_\mathfrak p^{n'})$,
$w_\mathfrak p(M) = \mu(K_0')/\mu(K_M) = [K_0' : K_M\cap K_0']/[K_M : K_M \cap K_0']$. -/
@[kb "weil1982" "§3.5 (local weights) [unverified locator]"]
def locFrameWeight (M : LocFrameSet v T Q') : ℝ :=
  ((stabilizer (orthGroup Q' Fv) M).relIndex (stdStab Q' v) : ℝ) /
    ((stdStab Q' v).relIndex (stabilizer (orthGroup Q' Fv) M) : ℝ)

/-- **The local type sum** $W_\mathfrak p = \sum_t w_\mathfrak p(M_t)$. -/
@[kb "weil1982" "§3.5 (local type sum) [unverified locator]"]
def locFrameTypeSum : ℝ := ∑ᶠ t : LocFrameTypes v T Q', locFrameWeight v T Q' (locFrameRep v T Q' t)

theorem stabilizer_locFrameStdPt : stabilizer (orthGroup Q' Fv) (locFrameStdPt v T Q') = stdStab Q' v := by
  ext h
  rw [mem_stabilizer_iff, ← mem_stdStab_orthEmbB_iff T Q' v h]
  constructor
  · intro hh; exact congrArg Subtype.val hh
  · intro hh; exact Subtype.ext hh

theorem locFrameWeight_std : locFrameWeight v T Q' (locFrameStdPt v T Q') = 1 := by
  simp [locFrameWeight, stabilizer_locFrameStdPt]

/-- If $\mathfrak o_\mathfrak p^{r+n'}$ is the only local type, $W_\mathfrak p = 1$. -/
theorem locFrameTypeSum_eq_one_of_transitive
    (h : ∀ M : LocFrameSet v T Q', ∃ g : orthGroup Q' Fv, g • locFrameStdPt v T Q' = M) :
    locFrameTypeSum v T Q' = 1 := by
  have hs : ∀ t : LocFrameTypes v T Q', t = Quotient.mk'' (locFrameStdPt v T Q') := by
    intro t
    induction t using Quotient.inductionOn' with
    | h M =>
      obtain ⟨g, hg⟩ := h M
      exact Quotient.sound' ⟨g, hg⟩
  have : Unique (LocFrameTypes v T Q') := ⟨⟨Quotient.mk'' (locFrameStdPt v T Q')⟩, hs⟩
  rw [locFrameTypeSum, finsum_unique, show (default : LocFrameTypes v T Q') = _ from hs default, locFrameRep_std,
    locFrameWeight_std]

end LocalTypes

/-! ### Frames, the integral group and the types -/

section Data

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T₀ : QuadForm (𝓞 F) r)
  (Q₀' : QuadForm (𝓞 F) n')

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "TF" => T₀.map (algebraMap (𝓞 F) F)
local notation "QF'" => Q₀'.map (algebraMap (𝓞 F) F)
local notation "QB" => blockForm TF QF'
local notation "Qo" => NF.Qp v (blockForm T₀ Q₀')
local notation "To" => NF.Qp v T₀

/-- The integral model of $T\perp Q'$ at $\mathfrak p$. -/
theorem isIntModel_blockForm : IsIntModel v QB Qo := fun y => by
  rw [← map_blockForm]; exact evalIn_coe_o v _ y

theorem fl_map_Qp {N : ℕ} (S₀ : QuadForm (𝓞 F) N) :
    (S₀.map (algebraMap (𝓞 F) F)).map (algebraMap F Fv) = (NF.Qp v S₀).map (algebraMap 𝔬 Fv) := by
  rw [QuadForm.map_map, QuadForm.map_map]; congr 1

theorem fl_QB_map : (QB).map (algebraMap F Fv) = (Qo).map (algebraMap 𝔬 Fv) := by
  rw [← map_blockForm, fl_map_Qp]

theorem fl_hess_ne {N : ℕ} (S₀ : QuadForm (𝓞 F) N) (hS : S₀.Nondegenerate) :
    (S₀.map (algebraMap (𝓞 F) F)).hessian.det ≠ 0 := by
  have : (S₀.map (algebraMap (𝓞 F) F)).hessian = S₀.hessian.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hS

theorem fl_hess_ne_v {N : ℕ} (S₀ : QuadForm (𝓞 F) N) (hS : S₀.Nondegenerate) :
    ((S₀.map (algebraMap (𝓞 F) F)).hessian.map (algebraMap F Fv)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).mpr (fl_hess_ne S₀ hS)

theorem fl_compMat_orth {N s : ℕ} (Q : QuadForm F N) {γ : GL (Fin N) Fv} (hγ : γ ∈ orthGroup Q Fv)
    (X : Matrix (Fin N) (Fin s) Fv) :
    (Q.map (algebraMap F Fv)).compMat (γ.val * X) = (Q.map (algebraMap F Fv)).compMat X := by
  refine QuadForm.eq_of_eval_eq fun y => ?_
  rw [QuadForm.eval_compMat, QuadForm.eval_compMat, ← mulVec_mulVec, ← evalIn_eq_eval_map, ← evalIn_eq_eval_map,
    evalIn_mulVec_of_mem Q hγ]

theorem fl_frame_gram : ((QB).map (algebraMap F Fv)).compMat (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) =
    (TF).map (algebraMap F Fv) := by
  rw [map_blockForm]; exact compMat_stdFrameMat _ _

/-- **$K = O(\mathfrak o_\mathfrak p^{r+n'})$ acting on integral frames** by left multiplication. -/
def frameRepK : stdStab QB v →* Matrix (Fin (r + n') × Fin r) (Fin (r + n') × Fin r) 𝔬 :=
  (frameHom r 𝔬).comp (intRep v QB)

/-- An integral frame as a matrix over $F_\mathfrak p$. -/
def coeFrame (x : Fin (r + n') × Fin r → 𝔬) : Matrix (Fin (r + n')) (Fin r) Fv := Matrix.of fun i j => (x (i, j) : Fv)

/-- The integral standard frame. -/
theorem coeFrame_stdFrame : coeFrame v (stdFrame (A := 𝔬) (r := r) (n' := n')) = stdFrameMat := by
  ext i j
  simp only [coeFrame, stdFrame, stdFrameMat, Matrix.of_apply]
  split_ifs <;> simp

/-- The lattice $g\,\mathfrak o_\mathfrak p^{r+n'}$ as a point of $Y_\mathfrak p$ when $g^{-1}E$ is integral. -/
def framePt (g : orthGroup QB Fv) (x : Fin (r + n') × Fin r → 𝔬)
    (hgx : ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * stdFrameMat = coeFrame v x) :
    LocFrameSet v TF QF' :=
  ⟨locAct v (g : GL (Fin (r + n')) Fv) (std v), ⟨g, rfl⟩, fun j => by
    refine ⟨((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *ᵥ stdCol v (n' := n') j, ?_, ?_⟩
    · rw [mulVec_stdCol, hgx]; exact coe_mem_std' v (fun i => x (i, j))
    · exact mulVec_inv_mulVec (g : GL (Fin (r + n')) Fv) (stdCol v (n' := n') j)⟩

/-- **Data of a local type:** every $M \in Y_\mathfrak p$ is $g\,\mathfrak o_\mathfrak p^{r+n'}$ with $g \in O(V)(F_\mathfrak p)$, and $x = g^{-1}E$ is an
integral frame of $T$. -/
theorem exists_frameType_data (M : LocFrameSet v TF QF') :
    ∃ (x : Fin (r + n') × Fin r → 𝔬) (g : orthGroup QB Fv), formF Qo x = tc To ∧
      locAct v (g : GL (Fin (r + n')) Fv) (std v) = M.1 ∧
      ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * stdFrameMat = coeFrame v x := by
  obtain ⟨g, hg⟩ := M.2.1
  have hcol : ∀ j, ∃ c : Fin (r + n') → 𝔬, (fun i => (c i : Fv)) =
      ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *ᵥ stdCol v (n' := n') j := by
    intro j
    have hm : stdCol v (n' := n') j ∈ locAct v (g : GL (Fin (r + n')) Fv) (std v) := hg ▸ M.2.2 j
    obtain ⟨y, hy, hgy⟩ := hm
    replace hgy : (g : GL (Fin (r + n')) Fv).val *ᵥ y = stdCol v (n' := n') j := hgy
    have hy' : ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *ᵥ stdCol v (n' := n') j = y := by
      rw [← hgy, mulVec_mulVec, ← Units.val_mul,
        show ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) * (g : GL (Fin (r + n')) Fv) = 1 from by
          rw [← Subgroup.coe_mul, inv_mul_cancel]; rfl,
        Units.val_one, one_mulVec]
    rw [hy']
    exact integral_of_mem_std' v hy
  choose c hc using hcol
  have hgx : ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) =
      coeFrame v (fun p : Fin (r + n') × Fin r => c p.2 p.1) := by
    refine Matrix.ext fun i j => ?_
    have h1 := congrFun (hc j) i
    rw [mulVec_stdCol] at h1
    exact h1.symm
  refine ⟨fun p => c p.2 p.1, g, ?_, hg, hgx⟩
  rw [formF_eq_tc_iff]
  refine NF.map_injective (f := algebraMap 𝔬 Fv) Subtype.val_injective ?_
  rw [← QuadForm.map_compMat, ← fl_QB_map, ← fl_map_Qp]
  have hX : (toMat (fun p : Fin (r + n') × Fin r => c p.2 p.1)).map (algebraMap 𝔬 Fv) =
      coeFrame v (fun p : Fin (r + n') × Fin r => c p.2 p.1) := rfl
  rw [hX, ← hgx, fl_compMat_orth v QB (g⁻¹ : orthGroup QB Fv).2, fl_frame_gram v T₀ Q₀']

/-- **Every integral frame of $T$ is $g^{-1}E$** for some $g \in O(V)(F_\mathfrak p)$ (Witt's theorem over $F_\mathfrak p$,
`exists_orthGroup_mul_stdFrameMat`). -/
theorem exists_frame_eq_inv_mul (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate) (y : Fin (r + n') × Fin r → 𝔬)
    (hy : formF Qo y = tc To) :
    ∃ g : orthGroup QB Fv, ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * stdFrameMat = coeFrame v y := by
  have hTF := fl_hess_ne_v v T₀ hT
  have hQF := fl_hess_ne_v v Q₀' hQ'
  have hQ : ((QB).hessian.map (algebraMap F Fv)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_hessian_blockForm]
    refine (map_ne_zero _).mpr (mul_ne_zero (fl_hess_ne T₀ hT) (fl_hess_ne Q₀' hQ'))
  have hX : ((QB).map (algebraMap F Fv)).compMat (coeFrame v y) = (TF).map (algebraMap F Fv) := by
    have e : (toMat y).map (algebraMap 𝔬 Fv) = coeFrame v y := rfl
    rw [fl_QB_map, ← e, QuadForm.map_compMat, (formF_eq_tc_iff _ _ _).mp hy]
    exact (fl_map_Qp v T₀).symm
  obtain ⟨γ, hγ⟩ := exists_orthGroup_mul_stdFrameMat TF QF' Fv hQ hTF hX
  exact ⟨γ⁻¹, by rw [inv_inv]; exact hγ⟩

/-- **Frames in one $K$-orbit give the same local type:** if $M = gL$, $M' = g'L$ and $\kappa \in K$ maps $g^{-1}E$ to $g'^{-1}E$, then
$M' \in O(Q')(F_\mathfrak p)\,M$ (`exists_orthEmbB_eq`). -/
theorem mem_orbit_of_frame (hT : T₀.Nondegenerate) (M M' : LocFrameSet v TF QF') (g g' : orthGroup QB Fv)
    (hg : locAct v (g : GL (Fin (r + n')) Fv) (std v) = M.1)
    (hg' : locAct v (g' : GL (Fin (r + n')) Fv) (std v) = M'.1) (κ : stdStab QB v)
    (hκ : ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * (((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)) =
        ((g'⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)) :
    M' ∈ orbit (orthGroup QF' Fv) M := by
  have hTF := fl_hess_ne_v v T₀ hT
  set γ : orthGroup QB Fv := g' * (κ : orthGroup QB Fv) * g⁻¹
  have hγ : (γ : GL (Fin (r + n')) Fv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) = stdFrameMat := by
    simp only [γ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    rw [hκ, ← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    simp
  obtain ⟨h, hh⟩ := exists_orthEmbB_eq TF QF' Fv hTF γ hγ
  refine ⟨h, Subtype.ext ?_⟩
  rw [LocFrameSet.smul_val, hh, ← hg, ← hg', ← locAct_mul]
  have : ((γ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) * (g : GL (Fin (r + n')) Fv) =
      (g' : GL (Fin (r + n')) Fv) * ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) := by
    simp only [γ, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  rw [this, locAct_mul, show locAct v ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v) = std v from κ.2]

end Data

end QuadFormsKB.Tamagawa.Frames
