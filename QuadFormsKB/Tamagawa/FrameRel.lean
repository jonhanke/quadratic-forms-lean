/-
# REL for frames: the lattice change of orbit counts of frames

**Layer:** first an abstract group with two groups of integral isometries acting on frames (a complete DVR $R$, every residue
characteristic), then the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ of a number field at a finite prime with the
stabilizers $K_1 = K(P\mathfrak o_\mathfrak p^N) $, $K_2 = K(\mathfrak o_\mathfrak p^N)$ of two lattices.

For lattices $\Lambda_1 = P\Lambda_2 \subseteq \Lambda_2$ and a form $T$ of rank $r$, a **frame** is an $N\times r$ matrix
$X$ (written as a vector indexed by $\mathrm{Fin}\,N\times\mathrm{Fin}\,r$) with $Q\circ X = T$. This file ports
`rel_nearCount` and `rel_local` (vectors, $r = 1$) to frames, acting by left multiplication (`frameMat`).

**Proves**
* `frameRel_gNear` (**REL for frames**): with $J = K_1\cap K_2$ and $y$ a frame of $T$ for $Q\circ P$,
  $N_1(K_1y)\,[\mathrm{St}_{K_1}y : \mathrm{St}_Jy]\,[K_2:J] = |\ker(P \bmod \pi^k)|^r\,[K_1:J]\,N_2(K_2Py)\,[\mathrm{St}_{K_2}Py : \mathrm{St}_Jy]$:
  the orbit comparison `gNear_mul_relIndex` in each lattice (openness by `exists_frame_openMat`), the image identity
  $P(Jy) = J(Py)$, saturation of the $J$-orbit in the coordinates of $\Lambda_2$, and the lattice change `gNear_comp_mulVec`
  (Hensel for frames, `exists_mem_of_near_frame`);
* `frameRel_local`: the same for $K_1 = K(P\mathfrak o_\mathfrak p^N)$, $K_2 = K(\mathfrak o_\mathfrak p^N)$ of a nondegenerate integral model,
  acting through `repAt`, `repStd`.

Sources: Weil 1982, §3.4 [unverified]. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.AlphaLaw
import QuadFormsKB.Tamagawa.FrameHensel
import QuadFormsKB.Tamagawa.FrameOpen

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.Tamagawa

/-! ### REL for frames (abstract form) -/

section RelAbstract

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {N r : ℕ}
  [Finite (IsLocalRing.ResidueField R)] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {G : Type*} [Group G] (K₁ K₂ : Subgroup G)
  (ρ₁ : K₁ →* Matrix (Fin N) (Fin N) R) (ρ₂ : K₂ →* Matrix (Fin N) (Fin N) R)

/-- **REL for frames: the lattice change of orbit counts** (Weil 1982, §3.4 [unverified]). Abstract setting as in
`rel_nearCount`: $K_1, K_2$ are subgroups of a group $G$ (the stabilizers of $\Lambda_1 = PR^N \subseteq \Lambda_2 = R^N$ in
$O(V)$), acting on $\Lambda_1$, $\Lambda_2$ by all integral isometries of $Q\circ P$, resp. $Q$ ($\rho_1$, $\rho_2$), compatibly
on $J = K_1\cap K_2$ ($P\rho_1 = \rho_2P$), and elements $\equiv 1 \bmod \pi^d$ of either lie in the other. They act on frames
$y \in R^{\mathrm{Fin}\,N\times\mathrm{Fin}\,r}$ by left multiplication (`frameHom`).
Let $T$ be a form of rank $r$ with $T\circ P_d = \langle d_0,\dots,d_{r-1}\rangle$ ($\det P_d \ne 0$, $d_i \ne 0$,
$\pi^{f+1}\nmid 4d_i$), $\pi^{d_T}\,\Vert\,\det H_T$, and $y$ a frame with $(Q\circ P)\circ y = T$. For $s \ge rf + 1 + d$,
$k \ge s + c + d_T$, $k \ge 2d_T + 1$:
$$N^{Q\circ P}_{k,s}(K_1y)\cdot[\mathrm{St}_{K_1}y : \mathrm{St}_{K_1}y\cap J]\cdot[K_2 : J]
  = |\ker(P\bmod\pi^k)|^r\cdot[K_1:J]\cdot N^Q_{k,s}(K_2Py)\cdot[\mathrm{St}_{K_2}Py : \mathrm{St}_{K_2}Py\cap J].$$
*Update:* the exponent $r$ on the kernel is the number of columns of the frame; for $r = 1$ this is `rel_nearCount`. -/
@[kb "weil1982" "§3.4 (orbit measures under a change of lattice, frames) [unverified]"]
theorem frameRel_gNear {π : R} (hπ : Irreducible π) (Q : QuadForm R N) (P : Matrix (Fin N) (Fin N) R)
    (hP : P.det ≠ 0) {c : ℕ} (hc : ∀ u : Fin N → R, ∃ w, P *ᵥ w = π ^ c • u)
    (hρ₁ : ∀ κ, (Q.compMat P).compMat (ρ₁ κ) = Q.compMat P) (hρ₂ : ∀ κ, Q.compMat (ρ₂ κ) = Q)
    (hsurj₁ : ∀ X, (Q.compMat P).compMat X = Q.compMat P → ∃ κ, ρ₁ κ = X)
    (hsurj₂ : ∀ X, Q.compMat X = Q → ∃ κ, ρ₂ κ = X)
    (hcompat : ∀ (g : G) (h₁ : g ∈ K₁) (h₂ : g ∈ K₂), P * ρ₁ ⟨g, h₁⟩ = ρ₂ ⟨g, h₂⟩ * P)
    {d : ℕ} (hJ₁ : ∀ κ : K₁, (∀ i j, π ^ d ∣ ρ₁ κ i j - (1 : Matrix (Fin N) (Fin N) R) i j) → (κ : G) ∈ K₂)
    (hJ₂ : ∀ κ : K₂, (∀ i j, π ^ d ∣ ρ₂ κ i j - (1 : Matrix (Fin N) (Fin N) R) i j) → (κ : G) ∈ K₁)
    (T : QuadForm R r) {Pd : Matrix (Fin r) (Fin r) R} (hPd : Pd.det ≠ 0) {dg : Fin r → R}
    (hPdg : T.compMat Pd = QuadForm.diag dg) (hdg : ∀ i, dg i ≠ 0) {f : ℕ} (hf : ∀ i, ¬ π ^ (f + 1) ∣ 4 * dg i)
    {dT : ℕ} (hd : π ^ dT ∣ T.hessian.det) (hd' : ¬ π ^ (dT + 1) ∣ T.hessian.det)
    (y : Fin N × Fin r → R) (hy : formF (Q.compMat P) y = tc T)
    {k s : ℕ} (hs : r * f + 1 + d ≤ s) (hk : s + c + dT ≤ k) (hk2 : 2 * dT + 1 ≤ k) :
    gNear (formF (Q.compMat P)) (tc T) π k s (gOrbit ((frameHom r R).comp ρ₁) ⊤ y) *
        (K₂.subgroupOf K₁).relIndex (gStab ((frameHom r R).comp ρ₁) y) * K₁.relIndex K₂ =
      Nat.card (redMat π k P).ker ^ r * K₂.relIndex K₁ *
        gNear (formF Q) (tc T) π k s (gOrbit ((frameHom r R).comp ρ₂) ⊤ (frameMat r P *ᵥ y)) *
        (K₁.subgroupOf K₂).relIndex (gStab ((frameHom r R).comp ρ₂) (frameMat r P *ᵥ y)) := by
  classical
  set Q₁ := Q.compMat P with hQ₁
  set J₁ := K₂.subgroupOf K₁ with hJ₁def
  set J₂ := K₁.subgroupOf K₂ with hJ₂def
  have hsk : s ≤ k := by omega
  have hy2 : formF Q (frameMat r P *ᵥ y) = tc T := by rw [formF_frameMat]; exact hy
  have hΦ₁ : ∀ κ (x : Fin N × Fin r → R), formF Q₁ (frameMat r (ρ₁ κ) *ᵥ x) = formF Q₁ x :=
    fun κ x => formF_frameMat_of_compMat Q₁ (hρ₁ κ) x
  have hΦ₂ : ∀ κ (x : Fin N × Fin r → R), formF Q (frameMat r (ρ₂ κ) *ᵥ x) = formF Q x :=
    fun κ x => formF_frameMat_of_compMat Q (hρ₂ κ) x
  -- compatibility on frames
  have hcv : ∀ (g : G) (h₁ : g ∈ K₁) (h₂ : g ∈ K₂) (z : Fin N × Fin r → R),
      frameMat r P *ᵥ (frameMat r (ρ₁ ⟨g, h₁⟩) *ᵥ z) = frameMat r (ρ₂ ⟨g, h₂⟩) *ᵥ (frameMat r P *ᵥ z) := by
    intro g h₁ h₂ z
    rw [mulVec_mulVec, mulVec_mulVec, ← frameMat_mul, ← frameMat_mul, hcompat g h₁ h₂]
  -- openness in the coordinates of `Λ₁`
  have hopen₁ : ∀ κ ∈ gCongr ((frameHom r R).comp ρ₁) π s y, ∃ γ ∈ J₁,
      ((frameHom r R).comp ρ₁) γ *ᵥ y = ((frameHom r R).comp ρ₁) κ *ᵥ y := by
    intro κ hκ
    obtain ⟨M, hM, hMy, hM1⟩ := exists_frame_openMat hπ Q₁ T hPd hPdg hdg hf (s := s) (by omega)
      (x := y) (x' := frameMat r (ρ₁ κ) *ᵥ y) hy ((hΦ₁ κ y).trans hy) (fun i => hκ i)
    obtain ⟨γ, rfl⟩ := hsurj₁ M hM
    exact ⟨γ, hJ₁ γ fun i j => (pow_dvd_pow π (by omega)).trans (hM1 i j), hMy⟩
  have hopen₂ : ∀ κ ∈ gCongr ((frameHom r R).comp ρ₂) π s (frameMat r P *ᵥ y), ∃ γ ∈ J₂,
      ((frameHom r R).comp ρ₂) γ *ᵥ (frameMat r P *ᵥ y) =
        ((frameHom r R).comp ρ₂) κ *ᵥ (frameMat r P *ᵥ y) := by
    intro κ hκ
    obtain ⟨M, hM, hMy, hM1⟩ := exists_frame_openMat hπ Q T hPd hPdg hdg hf (s := s) (by omega)
      (x := frameMat r P *ᵥ y) (x' := frameMat r (ρ₂ κ) *ᵥ (frameMat r P *ᵥ y)) hy2
      ((hΦ₂ κ _).trans hy2) (fun i => hκ i)
    obtain ⟨γ, rfl⟩ := hsurj₂ M hM
    exact ⟨γ, hJ₂ γ fun i j => (pow_dvd_pow π (by omega)).trans (hM1 i j), hMy⟩
  -- the orbit comparison in each lattice
  have hc₁ := gNear_mul_relIndex ((frameHom r R).comp ρ₁) (isCongr_formF (r := r) Q₁ π)
    (fun κ x => hΦ₁ κ x) (tc T) hsk hπ J₁ y hopen₁
  have hc₂ := gNear_mul_relIndex ((frameHom r R).comp ρ₂) (isCongr_formF (r := r) Q π)
    (fun κ x => hΦ₂ κ x) (tc T) hsk hπ J₂ (frameMat r P *ᵥ y) hopen₂
  -- `P (J y) = J (P y)`
  have himg : (frameMat r P *ᵥ ·) '' gOrbit ((frameHom r R).comp ρ₁) J₁ y =
      gOrbit ((frameHom r R).comp ρ₂) J₂ (frameMat r P *ᵥ y) := by
    ext z
    constructor
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      have hγ' : ((γ : K₁) : G) ∈ K₂ := Subgroup.mem_subgroupOf.mp hγ
      exact ⟨⟨γ, hγ'⟩, Subgroup.mem_subgroupOf.mpr γ.2, (hcv γ γ.2 hγ' y).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      have hγ' : ((γ : K₂) : G) ∈ K₁ := Subgroup.mem_subgroupOf.mp hγ
      exact ⟨frameMat r (ρ₁ ⟨γ, hγ'⟩) *ᵥ y, ⟨⟨γ, hγ'⟩, Subgroup.mem_subgroupOf.mpr γ.2, rfl⟩,
        hcv γ hγ' γ.2 y⟩
  -- the `J`-orbit is saturated in the coordinates of `Λ₂`
  have hsat : ∀ a ∈ gOrbit ((frameHom r R).comp ρ₁) J₁ y, ∀ z, formF Q z = tc T →
      (∀ i, π ^ (r * f + 1 + d) ∣ z i - (frameMat r P *ᵥ a) i) →
      ∃ a' ∈ gOrbit ((frameHom r R).comp ρ₁) J₁ y, z = frameMat r P *ᵥ a' := by
    rintro _ ⟨γ, hγ, rfl⟩ z hz hza
    have hγ2 : ((γ : K₁) : G) ∈ K₂ := hγ
    have e := hcv γ γ.2 hγ2 y
    have hza' : ∀ i, π ^ (r * f + 1 + d) ∣
        z i - (frameMat r (ρ₂ ⟨γ, hγ2⟩) *ᵥ (frameMat r P *ᵥ y)) i := fun i => by
      rw [← e]; exact hza i
    obtain ⟨M, hM, hMy, hM1⟩ := exists_frame_openMat hπ Q T hPd hPdg hdg hf
      (s := r * f + 1 + d) (by omega) (x := frameMat r (ρ₂ ⟨γ, hγ2⟩) *ᵥ (frameMat r P *ᵥ y)) (x' := z)
      ((hΦ₂ _ _).trans hy2) hz hza'
    obtain ⟨δ, rfl⟩ := hsurj₂ M hM
    have hδ1 : ((δ : K₂) : G) ∈ K₁ := hJ₂ δ fun i j => (pow_dvd_pow π (by omega)).trans (hM1 i j)
    have hγ1 : ((γ : K₁) : G) ∈ K₁ := γ.2
    have hg1 : (δ : G) * (γ : G) ∈ K₁ := K₁.mul_mem hδ1 hγ1
    have hg2 : (δ : G) * (γ : G) ∈ K₂ := K₂.mul_mem δ.2 hγ2
    refine ⟨frameMat r (ρ₁ ⟨(δ : G) * (γ : G), hg1⟩) *ᵥ y, ⟨⟨(δ : G) * (γ : G), hg1⟩, hg2, rfl⟩, ?_⟩
    rw [hcv _ hg1 hg2 y, ← hMy]
    have : (⟨(δ : G) * (γ : G), hg2⟩ : K₂) = δ * ⟨γ, hγ2⟩ := rfl
    rw [this, map_mul, frameMat_mul, ← mulVec_mulVec]
  -- the lattice change
  have hsat' : ∀ b ∈ (frameMat r P *ᵥ ·) '' gOrbit ((frameHom r R).comp ρ₁) J₁ y, ∀ z, formF Q z = tc T →
      (∀ i, π ^ (r * f + 1 + d) ∣ z i - b i) →
      z ∈ (frameMat r P *ᵥ ·) '' gOrbit ((frameHom r R).comp ρ₁) J₁ y := by
    rintro _ ⟨a, ha, rfl⟩ z hz hza
    obtain ⟨a', ha', rfl⟩ := hsat a ha z hz hza
    exact ⟨a', ha', rfl⟩
  have hlat := gNear_comp_mulVec hπ (isCongr_formF (r := r) Q π) (tc T) (frameMat r P)
    (frameMat_injective P hP) (frameMat_hc P hc) (A := gOrbit ((frameHom r R).comp ρ₁) J₁ y) (e := dT) hk
    (by
      intro z hz hza
      obtain ⟨a, ha, haz⟩ := hza
      obtain ⟨_, ⟨a', ha', rfl⟩, h⟩ := exists_mem_of_near_frame hπ Q T hd hd' hsat' hs (by omega) hk2 hz
        ⟨_, ⟨a, ha, rfl⟩, haz⟩
      exact ⟨a', ha', h⟩)
  simp only [formF_frameMat] at hlat
  rw [card_ker_frameMat, himg] at hlat
  -- assemble
  have e1 : J₁.index = K₂.relIndex K₁ := rfl
  have e2 : J₂.index = K₁.relIndex K₂ := rfl
  rw [e1] at hc₁
  rw [e2] at hc₂
  calc gNear (formF Q₁) (tc T) π k s (gOrbit ((frameHom r R).comp ρ₁) ⊤ y) *
        J₁.relIndex (gStab ((frameHom r R).comp ρ₁) y) * K₁.relIndex K₂
      = K₂.relIndex K₁ * gNear (formF Q₁) (tc T) π k s (gOrbit ((frameHom r R).comp ρ₁) J₁ y) *
          K₁.relIndex K₂ := by rw [hc₁]
    _ = K₂.relIndex K₁ * (Nat.card (redMat π k P).ker ^ r *
          gNear (formF Q) (tc T) π k s (gOrbit ((frameHom r R).comp ρ₂) J₂ (frameMat r P *ᵥ y))) *
          K₁.relIndex K₂ := by rw [hlat]
    _ = Nat.card (redMat π k P).ker ^ r * K₂.relIndex K₁ *
          (K₁.relIndex K₂ *
            gNear (formF Q) (tc T) π k s (gOrbit ((frameHom r R).comp ρ₂) J₂ (frameMat r P *ᵥ y))) := by ring
    _ = _ := by rw [← hc₂]; ring

end RelAbstract

/-! ### REL for frames in the local setting -/

section RelLocal

open NumberField IsDedekindDomain Lattices

variable {F : Type*} [Field F] [NumberField F] {N r : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **REL for frames for $\Lambda_1 = P\mathfrak o_\mathfrak p^N \subseteq \Lambda_2 = \mathfrak o_\mathfrak p^N$** in the local setting:
`frameRel_gNear` with $K_1 = K(\Lambda_1)$, $K_2 = K(\Lambda_2)$ acting through their integral matrices (`repAt`, `repStd`) on
frames of $T$ (a form of rank $r$ over $\mathfrak o_\mathfrak p$ with $T\circ P_d = \langle d_0,\dots,d_{r-1}\rangle$,
$\pi^{d_T}\,\Vert\,\det H_T$); $s \ge rf + 1 + c$ where $\det P \mid \pi^c$. -/
theorem frameRel_local (Qo : QuadForm 𝔬 N) (hQo : Qo.Nondegenerate) (P : Matrix (Fin N) (Fin N) 𝔬)
    (hP : P.det ≠ 0) {c : ℕ} (hc : P.det ∣ NF.π v ^ c)
    (T : QuadForm 𝔬 r) {Pd : Matrix (Fin r) (Fin r) 𝔬} (hPd : Pd.det ≠ 0) {dg : Fin r → 𝔬}
    (hPdg : T.compMat Pd = QuadForm.diag dg) (hdg : ∀ i, dg i ≠ 0) {f : ℕ}
    (hf : ∀ i, ¬ NF.π v ^ (f + 1) ∣ 4 * dg i) {dT : ℕ} (hd : NF.π v ^ dT ∣ T.hessian.det)
    (hd' : ¬ NF.π v ^ (dT + 1) ∣ T.hessian.det)
    (y : Fin N × Fin r → 𝔬) (hy : formF (Qo.compMat P) y = tc T) {k s : ℕ} (hs : r * f + 1 + c ≤ s)
    (hk : s + c + dT ≤ k) (hk2 : 2 * dT + 1 ≤ k) :
    gNear (formF (Qo.compMat P)) (tc T) (NF.π v) k s
        (gOrbit ((frameHom r 𝔬).comp (repAt v (Qo.map (algebraMap 𝔬 Fv)) (glOf v P hP))) ⊤ y) *
        ((KL v (Qo.map (algebraMap 𝔬 Fv)) (std v)).subgroupOf
          (KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v)))).relIndex
          (gStab ((frameHom r 𝔬).comp (repAt v (Qo.map (algebraMap 𝔬 Fv)) (glOf v P hP))) y) *
        (KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v))).relIndex
          (KL v (Qo.map (algebraMap 𝔬 Fv)) (std v)) =
      Nat.card (redMat (NF.π v) k P).ker ^ r *
        (KL v (Qo.map (algebraMap 𝔬 Fv)) (std v)).relIndex
          (KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v))) *
        gNear (formF Qo) (tc T) (NF.π v) k s
          (gOrbit ((frameHom r 𝔬).comp (repStd v (Qo.map (algebraMap 𝔬 Fv)))) ⊤ (frameMat r P *ᵥ y)) *
        ((KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v))).subgroupOf
          (KL v (Qo.map (algebraMap 𝔬 Fv)) (std v))).relIndex
          (gStab ((frameHom r 𝔬).comp (repStd v (Qo.map (algebraMap 𝔬 Fv)))) (frameMat r P *ᵥ y)) := by
  set Qv := Qo.map (algebraMap 𝔬 Fv)
  set h := glOf v P hP
  set K₁ := KL v Qv (locAct v h (std v))
  set K₂ := KL v Qv (std v)
  have hπ := NF.irreducible_π v
  have hQ₁ : (Qo.compMat P).map (algebraMap 𝔬 Fv) = Qv.compMat h.val := integralModel_compMat v rfl P hP
  have hQ₁nd := nondegenerate_compMat v hQo hP
  refine frameRel_gNear K₁ K₂ (repAt v Qv h) (repStd v Qv) hπ Qo P hP (exists_mulVec_eq_smul P hc)
    (compMat_repAt v h hQ₁) (compMat_repStd v rfl) (exists_repAt_eq v h hQ₁ hQ₁nd)
    (exists_repStd_eq v rfl hQo) ?_ ?_ ?_ T hPd hPdg hdg hf hd hd' y hy hs hk hk2
  · -- compatibility
    intro g h₁ h₂
    apply map_o_inj v
    show (P * repAt v Qv h ⟨g, h₁⟩).map _ = (repStd v Qv ⟨g, h₂⟩ * P).map _
    rw [Matrix.map_mul, Matrix.map_mul, repAt_map, repStd_map, ← glOf_val v P hP]
    simp only [Units.val_mul, ← Matrix.mul_assoc]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  · -- congruence elements of `K₁` lie in `K₂`
    intro κ hκ
    obtain ⟨E, hE⟩ := eq_one_add_of_dvd hκ
    obtain ⟨E', hE'⟩ : ∃ E', repAt v Qv h κ⁻¹ = 1 + NF.π v ^ c • E' :=
      ⟨_, inv_congr_one (by rw [← map_mul, inv_mul_cancel, map_one]) hE⟩
    obtain ⟨G₀, hG₀⟩ := exists_conj_integral v P hP hc E
    obtain ⟨G₁, hG₁⟩ := exists_conj_integral v P hP hc E'
    have hκv : ∀ κ' : K₁, (κ' : GL (Fin N) Fv).val = h.val * (repAt v Qv h κ').map (algebraMap 𝔬 Fv) * h⁻¹.val := by
      intro κ'
      rw [repAt_map]
      simp only [Units.val_mul, ← Matrix.mul_assoc]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.mul_one]
    refine mem_KL_std_of_integral v _ ((mem_KL v).mp κ.2).1 G₀ G₁ ?_ ?_
    · rw [hG₀, ← hE, ← hκv]
    · rw [hG₁, ← hE', ← hκv]; rfl
  · -- congruence elements of `K₂` lie in `K₁`
    intro κ hκ
    obtain ⟨E, hE⟩ := eq_one_add_of_dvd hκ
    obtain ⟨E', hE'⟩ : ∃ E', repStd v Qv κ⁻¹ = 1 + NF.π v ^ c • E' :=
      ⟨_, inv_congr_one (by rw [← map_mul, inv_mul_cancel, map_one]) hE⟩
    obtain ⟨G₀, hG₀⟩ := exists_conj_integral' v P hP hc E
    obtain ⟨G₁, hG₁⟩ := exists_conj_integral' v P hP hc E'
    have hκQ : Qv.compMat (κ : GL (Fin N) Fv).val = Qv := ((mem_KL v).mp κ.2).1
    have hmem : h⁻¹ * (κ : GL (Fin N) Fv) * h ∈ KL v (Qv.compMat h.val) (std v) := by
      refine mem_KL_std_of_integral v _ ?_ G₀ G₁ ?_ ?_
      · have e1 : h.val * (h⁻¹ * (κ : GL (Fin N) Fv) * h).val = (κ : GL (Fin N) Fv).val * h.val := by
          rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
        rw [compMat_mul, e1, ← compMat_mul, hκQ]
      · rw [hG₀, ← hE, repStd_map]; simp only [Units.val_mul]; rfl
      · rw [hG₁, ← hE', repStd_map]
        simp only [Units.val_mul, _root_.mul_inv_rev, inv_inv, InvMemClass.coe_inv, Matrix.mul_assoc]; rfl
    have : (κ : GL (Fin N) Fv) ∈ KL v Qv (locAct v h (std v)) := by
      rw [KL_locAct]
      refine ⟨_, hmem, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact this

end RelLocal

end QuadFormsKB.Tamagawa.Frames
