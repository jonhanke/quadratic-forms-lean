import QuadFormsKB.Tamagawa.Unitary.Global
import QuadFormsKB.Tamagawa.Unitary.SimilFinite
import QuadFormsKB.Tamagawa.FrameSiegel

/-!
# Unfolding $\tau(U(V))$: finiteness of the unitary class set and the covolume formula

**Layer:** Gan–Hanke–Yu's setting (Gan–Hanke–Yu 2001, §4) as in `Global.lean`: $F$ a totally real number field, $E = F(\omega)$, $\omega^2 = -D$,
$H_0$ an integral hermitian $m\times m$ matrix over $\mathcal O_F[\omega]$, nondegenerate and totally definite, $\Lambda = \mathcal O_F[\omega]^m$
(in the coordinates of the trace form $q(x) = h(x,x)$, $\Lambda = \mathcal O_F^{2m}$).

**Proves** (all unconditional, standard axioms only)
* `omegaR_transpose_hessian`: $\omega^{\mathsf T}S\omega = D\,S$ for the Hessian $S$ of the trace form ($q(\omega x) = N(\omega)q(x) = Dq(x)$);
* `bil_omega_conj`: for $\gamma\in O(V_F,q)$, $A = \gamma^{-1}\omega\gamma$ is a similitude of multiplier $D$;
* `omegaR_mulVec_mem_latSMul`, `omega_conj_mem`: $\omega(g\Lambda)\subseteq g\Lambda$ for $g\in U(V)(\mathbb A_f)$, so $\gamma^{-1}\omega\gamma$
  preserves $h_0\Lambda$ when $\gamma h_0\Lambda = g\Lambda$;
* **`finite_orbits_U`**: $U(V)(F)\backslash U(V)(\mathbb A_f)/U(\hat\Lambda)$ is finite (from the $O(V)$ class set, `finite_orbits`, and
  the finiteness of similitude endomorphisms, `finite_similEndo`); `finite_stabilizer_U`;
* `countable_GammaU`, `GammaU_inj`, `map_snd_GammaU`, `sigmaFinite_muFinU`, `isTotallyPosDef_traceQFF`;
* **`tauU_eq`** (the unfolding):
  $\tau(U(V)) = L(1,\chi)^{-1}|d_F|^{-m^2/2}\prod_\rho\mu_\rho(U(V)(F_\rho))\cdot\prod_v\mu_v(U(\Lambda_v))\cdot\mathrm{mass}$, with
  $\mathrm{mass} = \sum1/\#(U(V)(F)\cap\alpha U(\hat\Lambda)\alpha^{-1})$ (`dcMass`).
-/

open MeasureTheory Measure Topology Matrix Filter MulAction
open scoped ENNReal QuadraticAlgebra

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.ArchSOMeasure
  QuadFormsKB.Lattices QuadFormsKB.Siegel NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F) {m : ℕ} (H₀ : Matrix (Fin m) (Fin m) (QuadO D))

/-! ### $\omega$ is a similitude of multiplier $D$ for the trace form -/

/-- $\omega^{\mathsf T}S\,\omega = D\,S$ for the Gram matrix $S$ of the trace form, blockwise
$\begin{pmatrix}0&1\\-D&0\end{pmatrix}\begin{pmatrix}x&-Dy\\Dy&Dx\end{pmatrix}\begin{pmatrix}0&-D\\1&0\end{pmatrix} = D\begin{pmatrix}x&-Dy\\Dy&Dx\end{pmatrix}$. -/
theorem omegaO_transpose_traceS : (omegaO D m)ᵀ * traceS D H₀ * omegaO D m = D • traceS D H₀ := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, transpose_apply, omegaO, of_apply, ite_mul, zero_mul,
    mul_ite, mul_zero, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [traceS, blkO, Fin.sum_univ_two] <;> ring

/-- **$\omega^{\mathsf T}H\omega = D\,H$** for the Hessian $H$ of the trace form over $F$. -/
theorem omegaR_transpose_hessian :
    (omegaR D m F)ᵀ * (traceQFF D H₀).hessian * omegaR D m F = algebraMap (𝓞 F) F D • (traceQFF D H₀).hessian := by
  set S := reindex (eCoord m) (eCoord m) (traceS D H₀)
  set W := reindex (eCoord m) (eCoord m) (omegaO D m)
  have hW : Wᵀ * S * W = D • S := by
    simp only [S, W, reindex_apply]
    rw [transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, omegaO_transpose_traceS]
    rfl
  have hW' : Wᵀ * Sᵀ * W = D • Sᵀ := by
    have := congrArg transpose hW
    rwa [transpose_mul, transpose_mul, transpose_transpose, transpose_smul, ← Matrix.mul_assoc] at this
  have hH : (traceQFF D H₀).hessian = (S + Sᵀ).map (algebraMap (𝓞 F) F) := by
    rw [← hessian_traceQF]
    ext i j
    simp [traceQFF, QuadForm.hessian, QuadForm.map]
  have hO : omegaR D m F = W.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [omegaR, W]
  have hsum : Wᵀ * (S + Sᵀ) * W = D • (S + Sᵀ) := by
    rw [Matrix.mul_add, Matrix.add_mul, hW, hW', smul_add]
  rw [hH, hO, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hsum]
  ext i j
  simp [mul_add]

/-- $b(\omega x,\omega y) = D\,b(x,y)$ for the bilinear form $b(x,y) = x^{\mathsf T}Hy$ of the trace form. -/
theorem bil_omega (x y : Fin (m * 2) → F) :
    bil (traceQFF D H₀) (omegaR D m F *ᵥ x) (omegaR D m F *ᵥ y) =
      algebraMap (𝓞 F) F D * bil (traceQFF D H₀) x y := by
  simp only [bil]
  rw [mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
    omegaR_transpose_hessian, smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **$\gamma^{-1}\omega\gamma$ is a similitude of multiplier $D$** for $\gamma\in O(V_F, q)$. -/
theorem bil_omega_conj (γ : orthGroup (traceQFF D H₀) F) (x : Fin (m * 2) → F) :
    bil (traceQFF D H₀)
        ((((γ⁻¹ : orthGroup _ F) : GL (Fin (m * 2)) F).val * omegaR D m F * (γ : GL (Fin (m * 2)) F).val) *ᵥ x)
        ((((γ⁻¹ : orthGroup _ F) : GL (Fin (m * 2)) F).val * omegaR D m F * (γ : GL (Fin (m * 2)) F).val) *ᵥ x) =
      algebraMap (𝓞 F) F D * bil (traceQFF D H₀) x x := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, bil_isometry _ (γ⁻¹).2, bil_omega, bil_isometry _ γ.2]

/-! ### $\omega$ preserves the lattices $g\Lambda$, $g\in U(V)(\mathbb A_f)$ -/

local notation "QU" => traceQFF D H₀
local notation "LU" => stdLat F (m * 2)

/-- The local matrix of $\omega$ is the image of the rational one. -/
theorem omegaR_adic (v : HeightOneSpectrum (𝓞 F)) :
    omegaR D m (v.adicCompletion F) = (omegaR D m F).map (algebraMap F (v.adicCompletion F)) := by
  ext i j; simp [omegaR]

/-- $\omega$ maps $\mathfrak o_v^{2m}$ into itself (its entries are integral). -/
theorem omegaR_mulVec_mem_std (v : HeightOneSpectrum (𝓞 F)) {z : Fin (m * 2) → v.adicCompletion F}
    (hz : z ∈ std v) : omegaR D m (v.adicCompletion F) *ᵥ z ∈ std v := by
  refine mulVec_mem_std v (fun i j => ?_) hz
  simp only [omegaR, Matrix.map_apply]
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) F, valued_algebraMap_int]
  exact v.intValuation_le_one _

/-- **$\omega(g\Lambda)\subseteq g\Lambda$** for $g\in U(V)(\mathbb A_f)$: locally $\omega g_v\mathfrak o_v^{2m} = g_v\omega\mathfrak o_v^{2m}\subseteq g_v\mathfrak o_v^{2m}$. -/
theorem omegaR_mulVec_mem_latSMul (g : UAf D H₀) {y : Fin (m * 2) → F}
    (hy : y ∈ (latSMul QU (g : OAf QU) LU).1) : omegaR D m F *ᵥ y ∈ (latSMul QU (g : OAf QU) LU).1 := by
  rw [mem_iff_forall_loc (latSMul QU (g : OAf QU) LU).2] at hy ⊢
  intro v
  have hyv := hy v
  rw [loc_latSMul] at hyv ⊢
  have hstd : loc v (LU).1 = std v := loc_intVec v
  rw [hstd] at hyv ⊢
  obtain ⟨z, hz, hzy⟩ := mem_locAct.mp hyv
  refine mem_locAct.mpr ⟨omegaR D m (v.adicCompletion F) *ᵥ z, omegaR_mulVec_mem_std D v hz, ?_⟩
  have hc := (mem_unitaryOrth D).1 (g.2 v)
  rw [locVec_mulVec, ← omegaR_adic, ← hzy, mulVec_mulVec, mulVec_mulVec, hc]

/-- **The conjugate $\gamma^{-1}\omega\gamma$ preserves $h_0\Lambda$** when $\gamma h_0\in g\,O(\hat\Lambda)$ with $g\in U(V)(\mathbb A_f)$:
$\gamma h_0\Lambda = g\Lambda$ is $\omega$-stable. -/
theorem omega_conj_mem (g : UAf D H₀) (h₀ : OAf QU) (γ : orthGroup QU F)
    (h : (QuotientGroup.mk (diagF QU γ * h₀) : OAf QU ⧸ locStab QU LU) = QuotientGroup.mk (g : OAf QU))
    {x : Fin (m * 2) → F} (hx : x ∈ (latSMul QU h₀ LU).1) :
    ((((γ⁻¹ : orthGroup QU F) : GL (Fin (m * 2)) F).val * omegaR D m F * (γ : GL (Fin (m * 2)) F).val) *ᵥ x) ∈
      (latSMul QU h₀ LU).1 := by
  let _ : MulAction (OAf QU) (Lat F (m * 2)) := latAction QU
  rw [QuotientGroup.eq] at h
  set k := (diagF QU γ * h₀)⁻¹ * (g : OAf QU)
  have hk : k • LU = LU := by
    rw [← mem_stabilizer_iff, stabilizer_eq_locStab]; exact h
  have hg : (g : OAf QU) = diagF QU γ * h₀ * k := by simp only [k]; group
  have hgL : latSMul QU (g : OAf QU) LU = Lat.image (γ : GL (Fin (m * 2)) F) (latSMul QU h₀ LU) := by
    rw [← diagF_smul]
    change (g : OAf QU) • LU = diagF QU γ • h₀ • LU
    rw [hg, mul_smul, mul_smul, hk]
  have h1 : (γ : GL (Fin (m * 2)) F).val *ᵥ x ∈ (latSMul QU (g : OAf QU) LU).1 := by
    rw [hgL]; exact mulVec_mem_glImage hx
  have h2 := omegaR_mulVec_mem_latSMul D H₀ g h1
  rw [hgL] at h2
  obtain ⟨y, hy, hyx⟩ := mem_glImage.mp h2
  have : (((γ⁻¹ : orthGroup QU F) : GL (Fin (m * 2)) F).val * omegaR D m F * (γ : GL (Fin (m * 2)) F).val) *ᵥ x =
      y := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← hyx, mulVec_mulVec]
    simp
  rw [this]; exact hy

/-! ### The class set $U(V)(F)\backslash U(V)(\mathbb A_f)/U(\hat\Lambda)$ is finite -/

/-- The map $U(V)(\mathbb A_f)/U(\hat\Lambda)\to O(V)(\mathbb A_f)/O(\hat\Lambda)$ induced by the inclusion. -/
def classInc : UAf D H₀ ⧸ KU D H₀ → OAf QU ⧸ locStab QU LU :=
  Quotient.map' (fun a : UAf D H₀ => (a : OAf QU)) (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact hab)

theorem classInc_mk (a : UAf D H₀) :
    classInc D H₀ (QuotientGroup.mk a) = QuotientGroup.mk (a : OAf QU) := rfl

theorem classInc_injective : Function.Injective (classInc D H₀) := by
  intro a b hab
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  rw [classInc_mk, classInc_mk, QuotientGroup.eq] at hab
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using hab

theorem classInc_smul (γ : GammaUf D H₀) (y : UAf D H₀ ⧸ KU D H₀) :
    classInc D H₀ (γ • y) =
      (⟨((γ : UAf D H₀) : OAf QU), γ.2⟩ : ratPoints QU) • classInc D H₀ y := by
  induction y using QuotientGroup.induction_on with | H a => rfl

/-- A rational isometry commuting with $\omega$ is a rational point of $U(V)(\mathbb A_f)$. -/
theorem diagF_mem_uAf {δ : orthGroup QU F}
    (hδ : (δ : GL (Fin (m * 2)) F).val * omegaR D m F = omegaR D m F * (δ : GL (Fin (m * 2)) F).val) :
    diagF QU δ ∈ uAf D H₀ := fun v => by
  show orthMap QU (v.adicCompletion F) δ ∈ unitaryOrth D H₀ (v.adicCompletion F)
  rw [mem_unitaryOrth, orthMap_val, omegaR_adic, ← Matrix.map_mul, ← Matrix.map_mul, hδ]

/-- **Finitely many classes in the genus of $\Lambda$ for $U(V)$:** $U(V)(F)\backslash U(V)(\mathbb A_f)/U(\hat\Lambda)$ is finite
($H_0$ totally definite). *Proof.* The $O(V_F,q)(F)$-orbits on $O(V)(\mathbb A_f)/O(\hat\Lambda)$ are finite (`finite_orbits`). In a
fixed orbit, with representative $h_0O(\hat\Lambda)$, write the image of $x = gU(\hat\Lambda)$ as $\gamma_xh_0O(\hat\Lambda)$; the matrix
$\gamma_x^{-1}\omega\gamma_x$ preserves the lattice $h_0\Lambda$ (`omega_conj_mem`) and is a similitude of multiplier $D$
(`bil_omega_conj`), so it lies in a finite set (`finite_similEndo`); and if $\gamma_x^{-1}\omega\gamma_x = \gamma_{x'}^{-1}\omega\gamma_{x'}$, then
$\gamma_x\gamma_{x'}^{-1}$ commutes with $\omega$, so lies in $U(V)(F)$, and carries $x'$ to $x$. -/
@[kb "ganhankeyu2001" "(4.1), p. 109 (Mass(K) = Σ 1/#Γ_i over the finitely many double cosets)"]
theorem finite_orbits_U (hpd : IsTotallyPosDef QU) :
    Finite (orbitRel.Quotient (GammaUf D H₀) (UAf D H₀ ⧸ KU D H₀)) := by
  classical
  let _ : MulAction (OAf QU) (Lat F (m * 2)) := latAction QU
  set Y := OAf QU ⧸ locStab QU LU
  set X := UAf D H₀ ⧸ KU D H₀
  have hLi : IsIntegral QU (LU).1 := Frames.isIntegral_stdLat_self (traceQF D H₀)
  have hfinO : Finite (orbitRel.Quotient (ratPoints QU) Y) := finite_orbits hpd LU hLi
  -- representatives of the `O(V)(F)`-orbits
  let h₀ : orbitRel.Quotient (ratPoints QU) Y → OAf QU := fun o => (o.out : Y).out
  have hh₀ : ∀ o, (QuotientGroup.mk (h₀ o) : Y) = o.out := fun o => QuotientGroup.out_eq' _
  let oc : X → orbitRel.Quotient (ratPoints QU) Y := fun x => Quotient.mk'' (classInc D H₀ x)
  have hγ : ∀ x : X, ∃ γ : orthGroup QU F,
      (QuotientGroup.mk (diagF QU γ * h₀ (oc x)) : Y) = QuotientGroup.mk ((x.out : UAf D H₀) : OAf QU) := by
    intro x
    obtain ⟨r, hr⟩ := out_mem_orbit (oc x) (classInc D H₀ x) rfl
    obtain ⟨γ, hγ⟩ := (r⁻¹ : ratPoints QU).2
    refine ⟨γ, ?_⟩
    have hx : classInc D H₀ x = QuotientGroup.mk ((x.out : UAf D H₀) : OAf QU) := by
      conv_lhs => rw [← QuotientGroup.out_eq' x]
      rfl
    rw [← hx]
    have hr' : classInc D H₀ x = r⁻¹ • (oc x).out := by
      rw [← hr]; exact (inv_smul_smul r _).symm
    have e : (QuotientGroup.mk (diagF QU γ * h₀ (oc x)) : Y) = r⁻¹ • (QuotientGroup.mk (h₀ (oc x)) : Y) := by
      rw [hγ]; rfl
    rw [e, hh₀, ← hr']
  choose γ hγ using hγ
  let A : X → Matrix (Fin (m * 2)) (Fin (m * 2)) F := fun x =>
    ((γ x)⁻¹ : orthGroup QU F).1.val * omegaR D m F * (γ x : GL (Fin (m * 2)) F).val
  let T : orbitRel.Quotient (ratPoints QU) Y → Set (Matrix (Fin (m * 2)) (Fin (m * 2)) F) := fun o =>
    {B | (∀ y ∈ (latSMul QU (h₀ o) LU).1, B *ᵥ y ∈ (latSMul QU (h₀ o) LU).1) ∧
      ∀ y, bil QU (B *ᵥ y) (B *ᵥ y) = algebraMap (𝓞 F) F D * bil QU y y}
  have hT : ∀ o, (T o).Finite := by
    intro o
    have hgen : SameGenus QU (LU).1 (latSMul QU (h₀ o) LU).1 := by
      have hmem : latSMul QU (h₀ o) LU ∈ @MulAction.orbit (OAf QU) (Lat F (m * 2)) (latAction QU).toSMul LU :=
        ⟨h₀ o, rfl⟩
      rw [orbit_eq_genus QU LU] at hmem
      exact hmem
    exact finite_similEndo hpd (latSMul QU (h₀ o) LU).2 (hgen.isIntegral QU hLi) _
  let Φ : X → orbitRel.Quotient (ratPoints QU) Y × Matrix (Fin (m * 2)) (Fin (m * 2)) F := fun x => (oc x, A x)
  have hΦ : Set.range Φ ⊆ ⋃ o, (fun B => (o, B)) '' T o := by
    rintro _ ⟨x, rfl⟩
    refine Set.mem_iUnion.mpr ⟨oc x, A x, ⟨fun y hy => omega_conj_mem D H₀ x.out (h₀ (oc x)) (γ x) (hγ x) hy,
      fun y => bil_omega_conj D H₀ (γ x) y⟩, rfl⟩
  have hrange : (Set.range Φ).Finite := (Set.finite_iUnion fun o => (hT o).image _).subset hΦ
  -- equal data give the same `U(V)(F)`-orbit
  have hsame : ∀ x x' : X, Φ x = Φ x' → x ∈ orbit (GammaUf D H₀) x' := by
    intro x x' he
    have ho : oc x = oc x' := congrArg Prod.fst he
    have hA : A x = A x' := congrArg Prod.snd he
    set δ : orthGroup QU F := γ x * (γ x')⁻¹
    have hδ : (δ : GL (Fin (m * 2)) F).val * omegaR D m F = omegaR D m F * (δ : GL (Fin (m * 2)) F).val := by
      set a : GL (Fin (m * 2)) F := (γ x : GL (Fin (m * 2)) F)
      set b : GL (Fin (m * 2)) F := (γ x' : GL (Fin (m * 2)) F)
      have hA' : (a⁻¹).val * omegaR D m F * a.val = (b⁻¹).val * omegaR D m F * b.val := by
        simpa only [A, Subgroup.coe_inv] using hA
      have hδa : (δ : GL (Fin (m * 2)) F) = a * b⁻¹ := by simp [δ, a, b]
      rw [hδa]
      calc (a * b⁻¹).val * omegaR D m F = a.val * ((b⁻¹).val * omegaR D m F * b.val) * (b⁻¹).val := by
            simp [Matrix.mul_assoc]
        _ = a.val * ((a⁻¹).val * omegaR D m F * a.val) * (b⁻¹).val := by rw [hA']
        _ = omegaR D m F * (a * b⁻¹).val := by simp [Matrix.mul_assoc]
    let δU : GammaUf D H₀ := ⟨⟨diagF QU δ, diagF_mem_uAf D H₀ hδ⟩, ⟨δ, rfl⟩⟩
    refine ⟨δU, classInc_injective D H₀ ?_⟩
    rw [classInc_smul]
    have e1 : classInc D H₀ x = QuotientGroup.mk (diagF QU (γ x) * h₀ (oc x)) := by
      rw [hγ x, ← classInc_mk, QuotientGroup.out_eq']
    have e2 : classInc D H₀ x' = QuotientGroup.mk (diagF QU (γ x') * h₀ (oc x')) := by
      rw [hγ x', ← classInc_mk, QuotientGroup.out_eq']
    rw [e1, e2, ← ho]
    show (QuotientGroup.mk (diagF QU δ * (diagF QU (γ x') * h₀ (oc x))) : Y) = _
    simp only [δ, map_mul, map_inv, ← mul_assoc, inv_mul_cancel_right]
  have := hrange.to_subtype
  refine Finite.of_surjective (fun s : Set.range Φ => (Quotient.mk'' (Classical.choose s.2) :
    orbitRel.Quotient (GammaUf D H₀) X)) ?_
  intro q
  induction q using Quotient.inductionOn' with | h x => ?_
  refine ⟨⟨Φ x, x, rfl⟩, ?_⟩
  apply Quotient.sound'
  exact hsame _ _ (Classical.choose_spec (⟨x, rfl⟩ : Φ x ∈ Set.range Φ))

/-- **Finite stabilizers:** $U(V)(F)\cap\alpha\,U(\hat\Lambda)\alpha^{-1}$ is finite (it embeds in the finite group
$O(V_F,q)(F)\cap\alpha\,O(\hat\Lambda)\alpha^{-1}$, `finite_stabilizer`). -/
theorem finite_stabilizer_U (hpd : IsTotallyPosDef QU) (x : UAf D H₀ ⧸ KU D H₀) :
    Finite (stabilizer (GammaUf D H₀) x) := by
  have hLi : IsIntegral QU (LU).1 := Frames.isIntegral_stdLat_self (traceQF D H₀)
  have hO := finite_stabilizer hpd LU hLi (classInc D H₀ x)
  have hmem : ∀ s : stabilizer (GammaUf D H₀) x,
      (⟨((s : GammaUf D H₀) : UAf D H₀), (s : GammaUf D H₀).2⟩ : ratPoints QU) ∈
        stabilizer (ratPoints QU) (classInc D H₀ x) := by
    intro s
    rw [mem_stabilizer_iff, ← classInc_smul]
    exact congrArg (classInc D H₀) s.2
  exact Finite.of_injective (fun s => (⟨_, hmem s⟩ : stabilizer (ratPoints QU) (classInc D H₀ x)))
    fun a b h => Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun t => ((t.1 : ratPoints QU) : OAf QU)) h)))

/-- A number field is countable. -/
local instance countable_numberField' : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem countable_unitaryOrth_F : Countable (unitaryOrth D H₀ F) := by
  have := countable_orthGroup (traceQF D H₀)
  exact Function.Injective.countable (f := fun g : unitaryOrth D H₀ F => (g : orthGroup QU F))
    Subtype.val_injective

/-- $U(V)(F)$ in $U(V)(\mathbb A_f)$ is countable. -/
theorem countable_GammaUf : Countable (GammaUf D H₀) := by
  have := countable_orthGroup (traceQF D H₀)
  have hR : Countable (ratPoints QU) := by
    have h : ((ratPoints QU : Subgroup (OAf QU)) : Set (OAf QU)) = Set.range (diagF QU) := MonoidHom.coe_range _
    exact (h ▸ Set.countable_range (diagF QU)).to_subtype
  exact Function.Injective.countable (f := fun γ : GammaUf D H₀ => (⟨((γ : UAf D H₀) : OAf QU), γ.2⟩ : ratPoints QU))
    fun a b h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))

/-- **$\mu_f$ is $\sigma$-finite:** $U(V)(\mathbb A_f) = \bigcup_{\gamma,\omega}\gamma\beta_\omega U(\hat\Lambda)$ is a countable union of translates of
the compact open $U(\hat\Lambda)$. -/
theorem sigmaFinite_muFinU (hpd : IsTotallyPosDef QU) (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    SigmaFinite (muFinU D H₀ lam) := by
  have := finite_orbits_U D H₀ hpd
  have := countable_GammaUf D H₀
  refine sigmaFinite_of_finite_dc (muFinU D H₀ lam) (GammaUf D H₀) (KU D H₀) ?_
  rw [muFinU_KU]; exact ENNReal.ofReal_lt_top

variable (hD : D ≠ 0) (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0)

theorem countable_GammaU : Countable (GammaU D H₀ hD hH hdet) := by
  have := countable_unitaryOrth_F D H₀
  have h : ((GammaU D H₀ hD hH hdet : Subgroup _) : Set (UAdele D H₀)) = Set.range (diagU D H₀ hD hH hdet) :=
    MonoidHom.coe_range _
  exact (h ▸ Set.countable_range (diagU D H₀ hD hH hdet)).to_subtype

/-- $U(V)(F)\to U(V)(\mathbb A_f)$ is injective. -/
theorem GammaU_inj : ∀ γ ∈ GammaU D H₀ hD hH hdet, γ.2 = 1 → γ = 1 := by
  rintro _ ⟨g, rfl⟩ h
  have h1 : diagF QU (g : orthGroup QU F) = 1 := congrArg Subtype.val h
  have hg : g = 1 := Subtype.ext (diagF_injective QU (h1.trans (map_one _).symm))
  rw [hg, map_one]

/-- **The finite-adelic projection of $U(V)(F)$ is `GammaUf`** (a rational isometry lying in $U(V)(\mathbb A_f)$ commutes with $\omega$). -/
theorem map_snd_GammaU : (GammaU D H₀ hD hH hdet).map (MonoidHom.snd _ _) = GammaUf D H₀ := by
  ext x
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨(g : orthGroup QU F), rfl⟩
  · rintro ⟨γ, hγ⟩
    obtain ⟨v₀⟩ := (nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)))
    have hγ' : diagF QU γ = (x : OAf QU) := hγ
    have hc : (γ : GL (Fin (m * 2)) F).val * omegaR D m F = omegaR D m F * (γ : GL (Fin (m * 2)) F).val := by
      have h : ((orthMap QU (v₀.adicCompletion F) γ : orthGroup QU _) : GL (Fin (m * 2)) _).val *
          omegaR D m (v₀.adicCompletion F) = omegaR D m (v₀.adicCompletion F) *
          ((orthMap QU (v₀.adicCompletion F) γ : orthGroup QU _) : GL (Fin (m * 2)) _).val := by
        have h0 := (mem_unitaryOrth D).1 (x.2 v₀)
        rw [← hγ'] at h0
        exact h0
      rw [orthMap_val, omegaR_adic, ← Matrix.map_mul, ← Matrix.map_mul] at h
      exact Matrix.map_injective (algebraMap F (v₀.adicCompletion F)).injective h
    refine ⟨_, ⟨⟨γ, hc⟩, rfl⟩, Subtype.ext hγ'⟩

/-- **Definite at every real place $\Rightarrow$ totally positive definite** ($F$ totally real): for $x\ne0$ and
$\sigma : F\to\mathbb C$, $\sigma(q(x)) = q^{\rho_\sigma}(\rho_\sigma(x)) > 0$. -/
theorem isTotallyPosDef_traceQFF [IsTotallyReal F] [∀ ρ : F →+* ℝ, Fact (IsPosDefR (traceQR D H₀ ρ))] :
    IsTotallyPosDef QU := by
  intro x hx σ
  have hy : (fun i => realEmb σ (x i)) ≠ 0 := by
    intro h; apply hx; funext i
    exact (realEmb σ).injective (by simpa using congrFun h i)
  have hpos := (Fact.out : IsPosDefR (traceQR D H₀ (realEmb σ))) _ hy
  rw [traceQR, Measure.eval_map_real] at hpos
  rw [← realEmb_apply]
  exact Complex.zero_lt_real.mpr hpos

/-! ### The unfolding of $\tau(U(V))$ -/

/-- **The unfolding of the covolume** (definite case): for $H_0$ totally definite,
$$\tau(U(V)) = L(1,\chi)^{-1}\,|d_F|^{-m^2/2}\prod_\rho\mu_\rho(U(V)(F_\rho))\cdot\prod_v\frac{\beta^h_v}{\lambda_v}\cdot
  \mathrm{mass}(U(V)(F)\backslash U(V)(\mathbb A_f)/U(\hat\Lambda)),$$
$\mathrm{mass} = \sum 1/\#(U(V)(F)\cap\alpha U(\hat\Lambda)\alpha^{-1})$ over the double cosets (`dcMass`; Gan–Hanke–Yu (4.1)), with
$\mu_\rho(U(V)(F_\rho))$ = `archDensityU` and $\prod_v\beta^h_v/\lambda_v$ = `finFactorU` (a convergent product,
`multipliable_hermDensity_div_lamL`). This is Weil's unfolding (Weil 1982, §2.4) as in `covolume_muAdele` for $SO(V)$. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)) [unverified]; ganhankeyu2001 (4.1), p. 109 (Mass(K))"]
theorem tauU_eq [∀ ρ : F →+* ℝ, Fact (IsPosDefR (traceQR D H₀ ρ))] (hpd : IsTotallyPosDef QU)
    (E : Type) [Field E] [NumberField E] [Algebra F E] :
    tauU D H₀ hD hH hdet E =
      ENNReal.ofReal (QuadFormsKB.RegProd.LOne (chiE F E))⁻¹ *
        ENNReal.ofReal (|(discr F : ℝ)| ^ (-((m : ℝ) ^ 2 / 2))) *
        (∏ ρ : F →+* ℝ, ENNReal.ofReal (archDensityU D H₀ ρ)) *
        ENNReal.ofReal (finFactorU D H₀ (lamL (chiE F E))) *
        ENNReal.ofReal (dcMass (GammaUf D H₀) (KU D H₀)) := by
  have := countable_GammaU D H₀ hD hH hdet
  have := sigmaFinite_muFinU D H₀ hpd (lamL (chiE F E))
  set μA : Measure (UInf D H₀) := ENNReal.ofReal (QuadFormsKB.RegProd.LOne (chiE F E))⁻¹ •
    ENNReal.ofReal (|(discr F : ℝ)| ^ (-((m : ℝ) ^ 2 / 2))) • Measure.pi fun ρ => muArchU D H₀ ρ
  have : ∀ ρ, IsFiniteMeasure (muArchU D H₀ ρ) := fun ρ => ⟨by rw [muArchU_univ]; exact ENNReal.ofReal_lt_top⟩
  have : SFinite μA := by simp only [μA]; infer_instance
  have : μA.IsMulLeftInvariant := by simp only [μA]; infer_instance
  have hμ : muTamU D H₀ E = μA.prod (muFinU D H₀ (lamL (chiE F E))) := by
    simp only [muTamU, μA, Measure.prod_smul_left]
  have hmap := map_snd_GammaU D H₀ hD hH hdet
  have hfin : Finite (orbitRel.Quotient ((GammaU D H₀ hD hH hdet).map (MonoidHom.snd _ _))
      (UAf D H₀ ⧸ KU D H₀)) := by
    rw [hmap]; exact finite_orbits_U D H₀ hpd
  have hstab : ∀ x : UAf D H₀ ⧸ KU D H₀,
      Finite (stabilizer ((GammaU D H₀ hD hH hdet).map (MonoidHom.snd _ _)) x) := by
    intro x; rw [hmap]; exact finite_stabilizer_U D H₀ hpd x
  unfold tauU
  rw [hμ, covolume_eq_measure_mul_dcMass_of_sep (GammaU D H₀ hD hH hdet) (KU D H₀) (isOpen_KU D H₀).measurableSet
    (sep_KU D H₀) (GammaU_inj D H₀ hD hH hdet) hstab μA _, hmap, muFinU_KU]
  simp only [μA, Measure.smul_apply, smul_eq_mul, Measure.pi_univ, muArchU_univ]
  ring

end QuadFormsKB.Tamagawa.Unitary
