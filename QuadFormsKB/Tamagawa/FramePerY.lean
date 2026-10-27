/-
# The per-frame identity

**Layer:** the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ of a number field at a finite prime (every residue
characteristic), forms over $\mathfrak o_\mathfrak p$ in coordinates.

This is the frame version of the `perY`. Let $\Lambda = \mathfrak o_\mathfrak p^{N}$ carry the integral form $Q_o$
($N = r + n'$) and
let $\Lambda_1 = P\,\mathfrak o_\mathfrak p^N \subseteq \Lambda$ be a sublattice in which the frame $Y = P E$ (with $E$ the standard frame,
the first $r$ columns of the identity) splits: $Q_o\circ P = T_o \perp Q''$. Then, for all large $s$ and $k$,
$$r\big(K(\Lambda_1)\cap\mathrm{St}(Y),\ K(\Lambda)\cap\mathrm{St}(Y)\big)\,\beta(Q_o)\,q^{kD} = N_{k,s}\big(K(\Lambda)\,PE\big)\,\|\det P\|^{n'+1}\,q^{dn'}\,\beta(Q''),$$
$D = Nr - r(r+1)/2$, $\pi^d\,\Vert\,\det H_{T_o}$. *Proof:* REL for frames (`frameRel_local`) at $y = E$ and the $\alpha$ law
(`AlphaLawAt`) turn the index ratio into the ratio of the near counts of the two orbits of $PE$ and $E$, and the orbit of $E$ in the
split lattice $\Lambda_1$ is counted by `frameNear_stdFrame`.

**Defines** `stabF v Y` $=\{g\in\mathrm{GL}_N(F_\mathfrak p) : gY = Y\}$, the stabilizer of a frame (the analogue of `stabV`).

**Proves** `gStab_repAt_map`, `gStab_repStd_map` (stabilizers of integral frames inside $K(\Lambda_i)$ are $K(\Lambda_i)\cap\mathrm{St}(Y)$),
`frameOrbit_repAt_eq` and **`perF`** (the per-frame identity).

Sources: Weil 1982, §3.4 and §4.5 [unverified]; Hanke 2004, §3, pp. 358–361. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameRel
import QuadFormsKB.Tamagawa.FrameLocalId
import QuadFormsKB.Tamagawa.FrameWeight
import QuadFormsKB.Tamagawa.OrbitalNonStd

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.Tamagawa Lattices NumberField IsDedekindDomain

/-! ### Stabilizers of a frame -/

section StabF

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N r n' : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The stabilizer of a frame** $Y \in F_\mathfrak p^{N\times r}$ in $\mathrm{GL}_N(F_\mathfrak p)$:
$\{g : gY = Y\}$ (columnwise: $g$ fixes each of the $r$ columns of $Y$). -/
def stabF (Y : Matrix (Fin N) (Fin r) Fv) : Subgroup (GL (Fin N) Fv) where
  carrier := {g | g.val * Y = Y}
  mul_mem' {a b} ha hb := by
    show (a * b).val * Y = Y
    rw [Units.val_mul, Matrix.mul_assoc, show b.val * Y = Y from hb, show a.val * Y = Y from ha]
  one_mem' := by show (1 : GL (Fin N) Fv).val * Y = Y; simp
  inv_mem' {a} ha := by
    show a⁻¹.val * Y = Y
    conv_lhs => rw [← show a.val * Y = Y from ha]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem mem_stabF {Y : Matrix (Fin N) (Fin r) Fv} {g : GL (Fin N) Fv} : g ∈ stabF v Y ↔ g.val * Y = Y := Iff.rfl

/-- Conjugation carries the stabilizer of $Y$ to the stabilizer of $hY$. -/
theorem stabF_map_conj (h : GL (Fin N) Fv) (Y : Matrix (Fin N) (Fin r) Fv) :
    (stabF v Y).map (MulAut.conj h).toMonoidHom = stabF v (h.val * Y) := by
  ext g
  rw [Subgroup.mem_map_equiv (f := MulAut.conj h), MulAut.conj_symm_apply, mem_stabF, mem_stabF]
  constructor
  · intro hg
    have := congrArg (h.val * ·) hg
    simp only [Units.val_mul, ← Matrix.mul_assoc] at this
    rwa [Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc] at this
  · intro hg
    simp only [Units.val_mul, Matrix.mul_assoc]
    rw [hg, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem pf_coeFrame_frameMat (P : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) (x : Fin (r + n') × Fin r → 𝔬) :
    coeFrame v (frameMat r P *ᵥ x) = P.map (algebraMap 𝔬 Fv) * coeFrame v x := by
  have e : ∀ y : Fin (r + n') × Fin r → 𝔬, coeFrame v y = (toMat y).map (algebraMap 𝔬 Fv) := fun y => rfl
  rw [e, e, toMat_frameMat_mulVec, Matrix.map_mul]

theorem pf_coeFrame_injective {x y : Fin (r + n') × Fin r → 𝔬} (h : coeFrame v x = coeFrame v y) : x = y := by
  funext p
  exact Subtype.ext (congrFun (congrFun h p.1) p.2)

/-- The stabilizer of an integral frame $u$ in $K(h\mathfrak o^N)$ (acting through `repAt`) maps onto
$K(h\mathfrak o^N)\cap\mathrm{St}(h\,u)$. -/
theorem gStab_repAt_map (Qv : QuadForm Fv (r + n')) (h : GL (Fin (r + n')) Fv) (u : Fin (r + n') × Fin r → 𝔬) :
    (gStab ((frameHom r 𝔬).comp (repAt v Qv h)) u).map (KL v Qv (locAct v h (std v))).subtype =
      KL v Qv (locAct v h (std v)) ⊓ stabF v (h.val * coeFrame v u) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_stabF]
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    refine ⟨κ.2, ?_⟩
    have h1 : frameMat r (repAt v Qv h κ) *ᵥ u = u := hκ
    have h2 := congrArg (coeFrame v) h1
    rw [pf_coeFrame_frameMat, repAt_map] at h2
    have := congrArg (h.val * ·) h2
    simp only [Units.val_mul, ← Matrix.mul_assoc] at this
    rwa [Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc] at this
  · rintro ⟨hg, hgw⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    show frameMat r (repAt v Qv h ⟨g, hg⟩) *ᵥ u = u
    apply pf_coeFrame_injective v
    rw [pf_coeFrame_frameMat, repAt_map]
    show (h⁻¹ * g * h).val * coeFrame v u = coeFrame v u
    simp only [Units.val_mul, Matrix.mul_assoc]
    rw [hgw, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- The stabilizer of an integral frame $u$ in $K(\mathfrak o^N)$ (through `repStd`) maps onto $K(\mathfrak o^N)\cap\mathrm{St}(u)$. -/
theorem gStab_repStd_map (Qv : QuadForm Fv (r + n')) (u : Fin (r + n') × Fin r → 𝔬) :
    (gStab ((frameHom r 𝔬).comp (repStd v Qv)) u).map (KL v Qv (std v)).subtype =
      KL v Qv (std v) ⊓ stabF v (coeFrame v u) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_stabF]
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    refine ⟨κ.2, ?_⟩
    have h1 : frameMat r (repStd v Qv κ) *ᵥ u = u := hκ
    have h2 := congrArg (coeFrame v) h1
    rwa [pf_coeFrame_frameMat, repStd_map] at h2
  · rintro ⟨hg, hgw⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    show frameMat r (repStd v Qv ⟨g, hg⟩) *ᵥ u = u
    apply pf_coeFrame_injective v
    rw [pf_coeFrame_frameMat, repStd_map]
    exact hgw

/-- **Two orbits of $E$ coincide:** in the lattice $P\mathfrak o^N$ the orbit of $E$ under the group $K(P\mathfrak o^N)$ (through `repAt`)
is the orbit under all integral isometries of $Q_o\circ P$. -/
theorem frameOrbit_repAt_eq (Qo : QuadForm 𝔬 (r + n')) (hQo : Qo.Nondegenerate)
    (P : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) (hP : P.det ≠ 0) (y : Fin (r + n') × Fin r → 𝔬) :
    gOrbit ((frameHom r 𝔬).comp (repAt v (Qo.map (algebraMap 𝔬 Fv)) (glOf v P hP))) ⊤ y =
      gOrbit (frameRep (Qo.compMat P) r) ⊤ y := by
  have hQ₁ : (Qo.compMat P).map (algebraMap 𝔬 Fv) = (Qo.map (algebraMap 𝔬 Fv)).compMat (glOf v P hP).val :=
    integralModel_compMat v rfl P hP
  have hnd := nondegenerate_compMat v hQo hP
  ext z
  constructor
  · rintro ⟨κ, -, rfl⟩
    exact ⟨isomOf hnd (repAt v (Qo.map (algebraMap 𝔬 Fv)) (glOf v P hP) κ)
      (compMat_repAt v (glOf v P hP) hQ₁ κ), Subgroup.mem_top _, rfl⟩
  · rintro ⟨κ, -, rfl⟩
    obtain ⟨κ', hκ'⟩ := exists_repAt_eq v (glOf v P hP) hQ₁ hnd (κ : GL (Fin (r + n')) 𝔬).val (compMat_frameRep _ κ)
    refine ⟨κ', Subgroup.mem_top _, ?_⟩
    show frameMat r (repAt v (Qo.map (algebraMap 𝔬 Fv)) (glOf v P hP) κ') *ᵥ y = _
    rw [hκ']
    rfl

end StabF

/-! ### The per-frame identity -/

section PerF

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {r n' : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The per-frame identity** (Weil 1982, §3.4 [unverified]; every prime where the $\alpha$ law holds). Let $Q_o$ over
$\mathfrak o_\mathfrak p$ be nondegenerate in $N = r + n'$ variables and $P$ integral with $\det P \ne 0$ and
$Q_o\circ P = T_o \perp Q''$ ($Q''$ nondegenerate; so the frame $Y = PE$ splits the sublattice $\Lambda_1 = P\mathfrak o_\mathfrak p^N$),
$\pi^d\,\Vert\,\det H_{T_o}$, and $T_o\circ P_d = \langle d_0,\dots,d_{r-1}\rangle$ a diagonalization. With $K_1 = K(\Lambda_1)$,
$K_2 = K(\mathfrak o_\mathfrak p^N)$: for all large $s$ and $k$,
$$r\big(K_1\cap\mathrm{St}(Y),\ K_2\cap\mathrm{St}(Y)\big)\,\beta(Q_o)\,q^{kD} = N_{k,s}(K_2\,PE)\,\|\det P\|^{n'+1}\,q^{dn'}\,\beta(Q''),$$
$D = Nr - r(r+1)/2$ (so $q^{kD}$ is the ratio of the normalizations of the densities of $Q_o$ and $Q''$). -/
theorem perF (Qo : QuadForm 𝔬 (r + n')) (hQo : Qo.Nondegenerate) (To : QuadForm 𝔬 r) (Q'' : QuadForm 𝔬 n')
    (hQ'' : Q''.Nondegenerate) {Pd : Matrix (Fin r) (Fin r) 𝔬} (hPd : Pd.det ≠ 0) {dg : Fin r → 𝔬}
    (hPdg : To.compMat Pd = QuadForm.diag dg) (hdg : ∀ i, dg i ≠ 0) {d : ℕ}
    (hd : NF.π v ^ d ∣ To.hessian.det) (hd' : ¬ NF.π v ^ (d + 1) ∣ To.hessian.det)
    (P : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) (hP : P.det ≠ 0) (hsplit : Qo.compMat P = blockForm To Q'')
    (hlaw : AlphaLawAt v Qo P hP) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ᶠ k in Filter.atTop,
      relRatio (KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v)) ⊓
          stabF v ((glOf v P hP).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)))
        (KL v (Qo.map (algebraMap 𝔬 Fv)) (std v) ⊓
          stabF v ((glOf v P hP).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv))) *
          localDensityForm Qo Qo (NF.π v) * (q 𝔬 : ℝ) ^ (k * ((r + n') * r - r * (r + 1) / 2)) =
        gNear (formF Qo) (tc To) (NF.π v) k s
            (gOrbit ((frameHom r 𝔬).comp (repStd v (Qo.map (algebraMap 𝔬 Fv)))) ⊤
              (frameMat r P *ᵥ (stdFrame : Fin (r + n') × Fin r → 𝔬))) *
          ‖((P.det : 𝔬) : Fv)‖ ^ (n' + 1) * (q 𝔬 : ℝ) ^ (d * n') * localDensityForm Q'' Q'' (NF.π v) := by
  classical
  have hπ := NF.irreducible_π v
  have h2 := NF.two_ne_zero' v
  have h4 : (4 : 𝔬) ≠ 0 := by
    rw [show (4 : 𝔬) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  set Qv := Qo.map (algebraMap 𝔬 Fv)
  set h := glOf v P hP
  set K₁ := KL v Qv (locAct v h (std v))
  set K₂ := KL v Qv (std v)
  set Y : Matrix (Fin (r + n')) (Fin r) Fv := h.val * stdFrameMat with hY
  obtain ⟨c, hc⟩ := dvd_pow_ord v hP
  choose fi hfi hfi' using fun i => exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h4 (hdg i))
  set f := Finset.univ.sup fi with hfdef
  have hf : ∀ i, ¬ NF.π v ^ (f + 1) ∣ 4 * dg i := fun i hh =>
    hfi' i ((pow_dvd_pow _ (by have := Finset.le_sup (f := fi) (Finset.mem_univ i); omega)).trans hh)
  obtain ⟨d', he, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hQ''
  obtain ⟨hdD, hdD'⟩ := det_blockForm_exact hπ To Q'' hd hd' he he'
  refine ⟨r * f + 1 + c, fun s hs => ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (s + c + d + 4 * (d + d') + 2 * d + 2 * d' + 1)] with k hk
  change relRatio (K₁ ⊓ stabF v Y) (K₂ ⊓ stabF v Y) * localDensityForm Qo Qo (NF.π v) *
    (q 𝔬 : ℝ) ^ (k * ((r + n') * r - r * (r + 1) / 2)) = _
  -- the stabilizers
  have hs₁ : (K₂.subgroupOf K₁).relIndex (gStab ((frameHom r 𝔬).comp (repAt v Qv h)) stdFrame) =
      (K₂ ⊓ stabF v Y).relIndex (K₁ ⊓ stabF v Y) :=
    relIndex_subgroupOf_eq K₁ K₂ _ _ (by rw [gStab_repAt_map, coeFrame_stdFrame]; rfl)
  have hs₂ : (K₁.subgroupOf K₂).relIndex (gStab ((frameHom r 𝔬).comp (repStd v Qv)) (frameMat r P *ᵥ stdFrame)) =
      (K₁ ⊓ stabF v Y).relIndex (K₂ ⊓ stabF v Y) :=
    relIndex_subgroupOf_eq K₂ K₁ _ _ (by rw [gStab_repStd_map, pf_coeFrame_frameMat, coeFrame_stdFrame]; rfl)
  -- REL for frames at `E`
  have hrel := frameRel_local v Qo hQo P hP hc To hPd hPdg hdg hf hd hd' stdFrame
    (by rw [hsplit]; exact formF_stdFrame To Q'') (s := s) (k := k) (by omega) (by omega) (by omega)
  rw [hs₁, hs₂] at hrel
  have horb := frameOrbit_repAt_eq v Qo hQo P hP stdFrame
  rw [horb] at hrel
  rw [hsplit] at hrel
  -- the orbit of `E` in the split lattice
  have hE := frameNear_stdFrame hπ To Q'' hd hd' he he' hPd hPdg hdg hf (s := s) (k := k) (by omega) (by omega)
  -- kernel
  have hind := QuadFormsKB.Tamagawa.card_ker_redMat_eq v P hP (k := k) (hc.trans (pow_dvd_pow _ (by omega)))
  -- densities
  have hβs : localDensityForm (blockForm To Q'') (blockForm To Q'') (NF.π v) =
      (Nat.card (orthMod (blockForm To Q'') (NF.π v) k) : ℝ) / (q 𝔬 : ℝ) ^ (k * ((r + n') * (r + n' - 1) / 2)) :=
    localDensityForm_self_eq_card _ _ hπ (d + d') hdD hdD' k (by omega)
  have hβ'' : localDensityForm Q'' Q'' (NF.π v) =
      (Nat.card (orthMod Q'' (NF.π v) k) : ℝ) / (q 𝔬 : ℝ) ^ (k * (n' * (n' - 1) / 2)) :=
    localDensityForm_self_eq_card _ _ hπ d' he he' k (by omega)
  have hβpos : 0 < localDensityForm (blockForm To Q'') (blockForm To Q'') (NF.π v) := by
    rw [← hsplit]
    exact localDensityForm_self_pos' v _ (nondegenerate_compMat v hQo hP)
  -- positivity
  have hlat : (locAct v h (std v)).IsLattice Fv := locAct_isLattice _ (std_isLattice v)
  have hcom := commens_KL v Qv hlat (std_isLattice v)
  have hcomS : Commens (K₁ ⊓ stabF v Y) (K₂ ⊓ stabF v Y) := commens_inf _ hcom
  have ha : (K₂.relIndex K₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcom.1
  have hb : (K₁.relIndex K₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcom.2
  have hs2 : ((K₁ ⊓ stabF v Y).relIndex (K₂ ⊓ stabF v Y) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcomS.2
  have hq : (0 : ℝ) < q 𝔬 := Nat.cast_pos.mpr q_pos
  have hD : 0 < ‖((P.det : 𝔬) : Fv)‖ := norm_pos_iff.mpr (fun h0 => hP (Subtype.ext (by simpa using h0)))
  -- the law
  unfold AlphaLawAt at hlaw
  rw [hsplit] at hlaw
  have hr2 : relRatio K₁ K₂ = (K₂.relIndex K₁ : ℝ) / (K₁.relIndex K₂ : ℝ) := rfl
  rw [hr2] at hlaw
  have hr1 : relRatio (K₁ ⊓ stabF v Y) (K₂ ⊓ stabF v Y) =
      ((K₂ ⊓ stabF v Y).relIndex (K₁ ⊓ stabF v Y) : ℝ) / ((K₁ ⊓ stabF v Y).relIndex (K₂ ⊓ stabF v Y) : ℝ) := rfl
  rw [hr1]
  -- cast the counting identities
  have hR := (by exact_mod_cast hrel :
    ((gNear (formF (blockForm To Q'')) (tc To) (NF.π v) k s (gOrbit (frameRep (blockForm To Q'') r) ⊤ stdFrame) : ℕ) : ℝ) *
        ((K₂ ⊓ stabF v Y).relIndex (K₁ ⊓ stabF v Y) : ℝ) * (K₁.relIndex K₂ : ℝ) =
      (Nat.card (redMat (NF.π v) k P).ker : ℝ) ^ r * (K₂.relIndex K₁ : ℝ) *
        (gNear (formF Qo) (tc To) (NF.π v) k s
          (gOrbit ((frameHom r 𝔬).comp (repStd v Qv)) ⊤ (frameMat r P *ᵥ stdFrame)) : ℝ) *
        ((K₁ ⊓ stabF v Y).relIndex (K₂ ⊓ stabF v Y) : ℝ))
  rw [hind] at hR
  have hEr := (by exact_mod_cast hE :
    ((gNear (formF (blockForm To Q'')) (tc To) (NF.π v) k s (gOrbit (frameRep (blockForm To Q'') r) ⊤ stdFrame) : ℕ) : ℝ) *
        ((q 𝔬 : ℝ) ^ (d * n') * (Nat.card (orthMod Q'' (NF.π v) k) : ℝ)) =
      (Nat.card (orthMod (blockForm To Q'') (NF.π v) k) : ℝ))
  -- exponents
  have hexp : k * ((r + n') * (r + n' - 1) / 2) =
      k * ((r + n') * r - r * (r + 1) / 2) + k * (n' * (n' - 1) / 2) := by
    rw [← mul_add]; congr 1; exact lid_tri r n'
  rw [hexp, pow_add] at hβs
  have hZ'' : (0 : ℝ) < (q 𝔬 : ℝ) ^ (k * (n' * (n' - 1) / 2)) := pow_pos hq _
  have hQ : (0 : ℝ) < (q 𝔬 : ℝ) ^ (k * ((r + n') * r - r * (r + 1) / 2)) := pow_pos hq _
  have hW : (0 : ℝ) < (q 𝔬 : ℝ) ^ (d * n') := pow_pos hq _
  -- the numbers
  generalize (q 𝔬 : ℝ) ^ (k * (n' * (n' - 1) / 2)) = Z'' at hZ'' hβs hβ''
  generalize (q 𝔬 : ℝ) ^ (k * ((r + n') * r - r * (r + 1) / 2)) = Q at hQ hβs ⊢
  generalize (q 𝔬 : ℝ) ^ (d * n') = W at hW hEr ⊢
  generalize (Nat.card (orthMod (blockForm To Q'') (NF.π v) k) : ℝ) = As at hβs hEr
  generalize (Nat.card (orthMod Q'' (NF.π v) k) : ℝ) = A'' at hβ'' hEr
  generalize localDensityForm (blockForm To Q'') (blockForm To Q'') (NF.π v) = Bs at hβs hβpos hlaw
  generalize localDensityForm Q'' Q'' (NF.π v) = B'' at hβ'' ⊢
  generalize localDensityForm Qo Qo (NF.π v) = B at hlaw ⊢
  generalize ‖((P.det : 𝔬) : Fv)‖ = Dp at hD hlaw hR ⊢
  generalize ((gNear (formF (blockForm To Q'')) (tc To) (NF.π v) k s
    (gOrbit (frameRep (blockForm To Q'') r) ⊤ stdFrame) : ℕ) : ℝ) = O₁ at hR hEr
  generalize (gNear (formF Qo) (tc To) (NF.π v) k s
    (gOrbit ((frameHom r 𝔬).comp (repStd v Qv)) ⊤ (frameMat r P *ᵥ stdFrame)) : ℝ) = N₂ at hR ⊢
  generalize ((K₂ ⊓ stabF v Y).relIndex (K₁ ⊓ stabF v Y) : ℝ) = s₁ at hR ⊢
  generalize ((K₁ ⊓ stabF v Y).relIndex (K₂ ⊓ stabF v Y) : ℝ) = s₂ at hR hs2 ⊢
  generalize (K₂.relIndex K₁ : ℝ) = a at hR hlaw ha
  generalize (K₁.relIndex K₂ : ℝ) = b at hR hlaw hb
  have hAs : As = Bs * (Z'' * Q) := by
    rw [hβs]; field_simp
  have hO₁ : O₁ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hEr
    have : 0 < As := by rw [hAs]; positivity
    linarith
  have hDr : Dp ^ (r + n' + 1) = Dp ^ r * Dp ^ (n' + 1) := by ring
  rw [hDr] at hlaw
  have hDr0 : Dp ^ r ≠ 0 := (pow_pos hD r).ne'
  rw [inv_pow] at hR
  generalize Dp ^ (n' + 1) = En at hlaw ⊢
  generalize Dp ^ r = Er at hlaw hR hDr0
  have hB : B = b * Bs * (Er * En) / a := by
    rw [eq_div_iff ha]
    field_simp at hlaw
    linear_combination hlaw
  have hs1 : s₁ = Er⁻¹ * a * N₂ * s₂ / (O₁ * b) := by
    rw [eq_div_iff (mul_ne_zero hO₁ hb)]
    linear_combination hR
  rw [hB, hs1, hβ'']
  have hA' : As = O₁ * (W * A'') := by linear_combination -hEr
  rw [hA'] at hAs
  field_simp
  linear_combination (-N₂ * En) * hAs

end PerF

end QuadFormsKB.Tamagawa.Frames
