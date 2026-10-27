/-
# Weil's orbital Euler product

**Setting** (`OrbitalEulerProduct`). $F$ totally real, $Q_0$ over $\mathcal O_F$ in $N = n + 1$ variables, totally
positive definite, $L = \mathcal O_F^N$, $\rho = \rho_k$ the representative of a totally positive square class,
$\mu = \mu_{\mathrm{Tam}}(K_{SO})$. The orbit identity reduces $\tau(SO(V)) = 2$ (given $\tau = 2$ for the
stabilizers) to the identity
$$2\mu\sum_{\mathfrak b}N\mathfrak b^{-N-2s}\sum_{\mathrm{cls}M}\frac{\#\{\eta\in\mathfrak b^{-1}M : Q(\eta) = \rho\}}{|O(M)|}
  = \tau'_\rho\,|d_F|^{-\frac{N-1}2}\prod_w\frac{2\pi^{N/2}\sigma_w(\rho)^{\frac N2+s}}{\Gamma(\frac N2)\sqrt{\det A_w}}\prod_vZ_\mathfrak p(s,\rho).$$
This file proves it.

**The argument** (Weil 1982, §4.5, p. 109, made combinatorial).
1. *Bridge* (`sphereCount_eq_repCount`): for $\mathfrak b = (\beta)$, $\#\{\eta\in\mathfrak b^{-1}M : Q(\eta) = \rho\} = r_M(\beta^2\rho)$.
2. *Coordinates* (`AdaptedFrame`): $Q\circ g = \langle\rho\rangle\perp Q_0'$; with $g_\beta = g\,\mathrm{diag}(\beta, 1, \dots, 1)$, $Q\circ g_\beta = \langle\beta^2\rho\rangle\perp Q_0'$,
   and the global reduction (`repMass_eq_mass_mul`) gives
   $\sum_Mr_M(\beta^2\rho)/|O(M)| = \mathrm{Mass}(Q_0')\cdot W_\mathfrak b$.
3. *Factorization* (`typeSum_eq_prodG`, `locTypeSumG_transport`, `locTypeSumG_unit`): $W_\mathfrak b = \prod_\mathfrak pW_\mathfrak p(\mathrm{ord}_\mathfrak p\mathfrak b)$ with
   $W_\mathfrak p(j) = W_\mathfrak p(g^{-1}L_\mathfrak p, \varpi^j)$, the local type sum of the vector $\varpi^je_0$ in the lattice $g^{-1}L_\mathfrak p$.
4. *Local identity* (`OrbitalLocalIdentityAt`):
   $W_\mathfrak p(j)\,\alpha_\mathfrak p(Q_0)\,|2\rho|_\mathfrak p^{N-1}|\det g|_\mathfrak p^{-N} = \alpha_\mathfrak p(Q_0')\,q^{j(N-2)}\,\beta_\mathfrak p(Q_0, \rho\varpi^{2j})$; **proved** at every
   prime where $g^{-1}L_\mathfrak p$ is the standard lattice and $\mathrm{ord}_\mathfrak p\rho \le 1$ (`orbitalLocalIdentityAt_std`, from the
   imprimitive identity, dyadic primes included), a named input at the finitely many other primes.
5. *Euler product* (`hasSum_fracIdeal`), the local spherical factors (`hasSum_levelTerm`), the product formula and the archimedean
   bookkeeping.
-/
import QuadFormsKB.Tamagawa.OrbitalFrame
import QuadFormsKB.Tamagawa.ImprimitiveOrbital
import QuadFormsKB.Tamagawa.SphericalFibration
import QuadFormsKB.Tamagawa.SphericalLocalFactor
import QuadFormsKB.Weil.ProductFormulas
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain

open NumberField Matrix MulAction Filter Topology
open scoped Real ENNReal nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices LocalDensity QuadForm IsDedekindDomain
open QuadFormsKB.HilbertModular QuadFormsKB.IdeleClass QuadFormsKB.AdditiveZeta QuadFormsKB.SphericalUnfold

/-! ### Step 1: the sphere counts of the classes are representation numbers -/

section Bridge

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

theorem qv_gramF (R : QuadForm (𝓞 F) n) (x : Fin n → F) :
    qv (gramF R) x = (R.map (algebraMap (𝓞 F) F)).eval x := by
  rw [QuadForm.eval, QuadForm.evalIn_eq_dotProduct, qv, gramF, QuadForm.hessian, Matrix.map_add _ (map_add _),
    Matrix.transpose_map, smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add]
  simp only [QuadForm.map, Algebra.algebraMap_self]
  generalize R.coeff.map (algebraMap (𝓞 F) F) = C
  have : x ⬝ᵥ Cᵀ *ᵥ x = x ⬝ᵥ C *ᵥ x := by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
  have h2 : C.map (RingHom.id F) = C := by ext; rfl
  rw [this, smul_eq_mul, h2]
  ring

/-- The class representative in the coordinates of `classForm`: $c.\mathrm{out} = \gamma\mathcal O_F^n$ and the class form is $Q\circ\gamma$. -/
theorem classForm_spec' (Q₀ : QuadForm (𝓞 F) n) (hfree : GenusFree (formF Q₀) (stdLat F n))
    {c : LatClass (formF Q₀)} (hc : c ∈ genusClasses (formF Q₀) (stdLat F n)) :
    ∃ (γ : GL (Fin n) F) (hi : IsIntegral (formF Q₀) (latOf γ)),
      c.out.1 = latOf γ ∧ classForm Q₀ c = gramZ (formF Q₀) γ hi := by
  classical
  have hg := sameGenus_out hc
  obtain ⟨γ, hγ⟩ := hfree c.out hg
  have hex : ∃ (γ : GL (Fin n) F) (_ : IsIntegral (formF Q₀) (latOf γ)), c.out.1 = latOf γ :=
    ⟨γ, hγ ▸ SameGenus.isIntegral _ (isIntegral_stdLat Q₀) hg, hγ⟩
  refine ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec, ?_⟩
  unfold classForm; simp only [hex, ↓reduceDIte]

theorem mem_inv_spanSingleton_iff {β : F} (hβ : β ≠ 0) (x : F) :
    x ∈ (((FractionalIdeal.spanSingleton (𝓞 F)⁰ β)⁻¹ * 1 : FractionalIdeal (𝓞 F)⁰ F) : Set F) ↔
      β * x ∈ (algebraMap (𝓞 F) F).range := by
  rw [mul_one, FractionalIdeal.spanSingleton_inv, SetLike.mem_coe, FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [Algebra.smul_def, ← mul_assoc, mul_comm β, mul_assoc, mul_inv_cancel₀ hβ, mul_one]
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [Algebra.smul_def, hz, mul_comm β, mul_assoc, mul_inv_cancel₀ hβ, mul_one]

/-- **Step 1: sphere counts are representation numbers** (for a principal $\mathfrak b = (\beta)$): with $c.\mathrm{out} = \gamma\mathcal O_F^n$ and the
class form $Q_\gamma = Q\circ\gamma$, $\eta \mapsto \gamma\beta\eta$ is a bijection
$\{\eta \in \mathfrak b^{-1}\mathcal O_F^n : Q_\gamma(\eta) = \rho\} \to \{w \in c.\mathrm{out} : Q(w) = \beta^2\rho\}$. -/
theorem sphereCount_eq_repCount (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (hfree : GenusFree (formF Q₀) (stdLat F n)) {c : LatClass (formF Q₀)} (hc : c ∈ genusClasses (formF Q₀) (stdLat F n))
    (𝔟 : FracIdeal F) {β : F} (hβ : β ≠ 0) (hb : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton _ β)
    (ρ : F) :
    sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) ρ 𝔟 = (repCount (formF Q₀) c.out (β ^ 2 * ρ) : ℝ≥0∞) := by
  have h1 := HilbertModular.sameGenus_out hc
  have h2 := HilbertModular.isIntegral_stdLat Q₀
  have hint : Lattices.IsIntegral (formF Q₀) c.out.1 := Lattices.SameGenus.isIntegral (formF Q₀) h2 h1
  have hfinR : Finite {w : Fin n → F // w ∈ c.out.1 ∧ (formF Q₀).eval w = β ^ 2 * ρ} :=
    finite_repSet hpd c.out.2 hint (β ^ 2 * ρ)
  classical
  obtain ⟨γ, hi, hout, hcf⟩ := classForm_spec' Q₀ hfree hc
  set P : (Fin n → F) → Prop := fun η => qv (gramF (classForm Q₀ c)) η = ρ ∧ LatMem (twist 𝔟 fun _ => 1) η
  have hP : ∀ η, P η ↔ (β • η) ∈ intVec ∧ (formF Q₀).eval (γ.val *ᵥ η) = ρ := by
    intro η
    simp only [P, hcf, qv_gramF, gramZ_map, eval_gramFormF_col, LatMem, twist]
    rw [and_comm]
    refine and_congr ?_ Iff.rfl
    refine forall_congr' fun i => ?_
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hb, Units.val_one, mem_inv_spanSingleton_iff hβ]
    rfl
  have hto : ∀ η : {η // P η}, γ.val *ᵥ (β • η.1) ∈ c.out.1 ∧ (formF Q₀).eval (γ.val *ᵥ (β • η.1)) = β ^ 2 * ρ := by
    intro η
    obtain ⟨h1, h2⟩ := (hP η.1).mp η.2
    refine ⟨hout ▸ mulVec_mem_glImage h1, ?_⟩
    rw [mulVec_smul, eval_smul_gen, h2]
  have hinv : ∀ w : {w : Fin n → F // w ∈ c.out.1 ∧ (formF Q₀).eval w = β ^ 2 * ρ},
      P (β⁻¹ • (γ⁻¹.val *ᵥ w.1)) := by
    intro w
    rw [hP]
    obtain ⟨hw, hQ⟩ := w.2
    have hw' : w.1 ∈ latOf γ := hout ▸ hw
    obtain ⟨y, hy, hyw⟩ := hw'
    have hy' : γ⁻¹.val *ᵥ w.1 = y := by
      rw [← hyw]
      show γ⁻¹.val *ᵥ (γ.val *ᵥ y) = y
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    refine ⟨?_, ?_⟩
    · rw [smul_smul, mul_inv_cancel₀ hβ, one_smul, hy']; exact hy
    · rw [mulVec_smul, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec,
        eval_smul_gen, hQ, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hβ), one_mul]
  let e : {η // P η} ≃ {w : Fin n → F // w ∈ c.out.1 ∧ (formF Q₀).eval w = β ^ 2 * ρ} :=
    { toFun := fun η => ⟨γ.val *ᵥ (β • η.1), hto η⟩
      invFun := fun w => ⟨β⁻¹ • (γ⁻¹.val *ᵥ w.1), hinv w⟩
      left_inv := fun η => Subtype.ext (show β⁻¹ • (γ⁻¹.val *ᵥ (γ.val *ᵥ (β • η.1))) = η.1 by
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, smul_smul,
          inv_mul_cancel₀ hβ, one_smul])
      right_inv := fun w => Subtype.ext (show γ.val *ᵥ (β • (β⁻¹ • (γ⁻¹.val *ᵥ w.1))) = w.1 by
        rw [smul_smul, mul_inv_cancel₀ hβ, one_smul, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, one_mulVec]) }
  have hfinP : Finite {η // P η} := Finite.of_equiv _ e.symm
  have hfinS : {η | P η}.Finite := Set.finite_coe_iff.mp hfinP
  unfold sphereCount
  rw [tsum_eq_sum (s := hfinS.toFinset) (fun η hη => by
    rw [Set.Finite.mem_toFinset] at hη; exact if_neg hη)]
  rw [Finset.sum_boole, Finset.filter_true_of_mem]
  · rw [repCount, ← Nat.card_congr e, show Nat.card {η // P η} = Nat.card ↥{η | P η} from rfl,
      Nat.card_eq_card_finite_toFinset hfinS]
  · intro η hη
    exact ((Set.Finite.mem_toFinset hfinS).mp hη : P η)

end Bridge

/-! ### Step 4: the local orbital identity for the frame lattice -/

section LocalFrame

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The uniformizer $\varpi = \pi_v$ of $\mathfrak o_\mathfrak p$, in $F_\mathfrak p$. -/
abbrev unifV : Fv := ((NF.π v : 𝔬) : Fv)

/-- **The frame lattice** $g^{-1}L_\mathfrak p$ ($L = \mathcal O_F^{n+1}$) in the adapted coordinates. -/
def frameLat (g : GL (Fin (n + 1)) F) : Submodule 𝔬 (Fin (n + 1) → Fv) := loc v (glImage g⁻¹ intVec)

/-- **The local type sum of the frame** at level $j \in \mathbb Z$: $W_\mathfrak p(j) = W_\mathfrak p(g^{-1}L_\mathfrak p, \varpi^j)$, the local types of the pairs
(lattice of the local genus of $g^{-1}L_\mathfrak p$, the vector $\varpi^je_0$), for $Q\circ g = \langle\rho\rangle\perp Q_0'$. -/
def locW {Q : QuadForm F (n + 1)} {ρ : F} (fr : AdaptedFrame Q ρ) (j : ℤ) : ℝ :=
  locTypeSumG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) (unifV v ^ j)

/-- **The local density at an element of $F_\mathfrak p$**: $\beta_\mathfrak p(L, t)$ for $t \in \mathfrak o_\mathfrak p$, and $0$ for $t \notin \mathfrak o_\mathfrak p$ (no vector of
$L_\mathfrak p$ has a non-integral value). -/
def betaZ {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (t : Fv) : ℝ :=
  if h : Valued.v t ≤ 1 then
    DVR.localDensity (NF.Qp v Q₀) (NF.π v) ⟨t, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h⟩
  else 0

/-- **Input (one prime): Weil's local orbital identity for the frame** (Weil 1982, §3.4 and §4.5, p. 109 [unverified]; Kitaoka
1993, §5.6 [unverified]). For $Q_0$ over $\mathcal O_F$ in $n + 1$ variables, $\rho \in F^\times$ and an adapted frame
$Q_0\circ g = \langle\rho\rangle\perp Q_0'$: for every $j \in \mathbb Z$,
$$W_\mathfrak p(j)\,\alpha_\mathfrak p(Q_0)\,|2\rho|_\mathfrak p^{\,n}\,|\det g|_\mathfrak p^{-(n+1)} = \alpha_\mathfrak p(Q_0')\,q^{j(n-1)}\,\beta_\mathfrak p(Q_0, \rho\varpi^{2j}),$$
$W_\mathfrak p(j)$ = `locW`, $\alpha_\mathfrak p$ = `NF.siegelDensity`, $\beta_\mathfrak p$ = `betaZ`, $|\cdot|_\mathfrak p$ Mathlib's normalized norm.

Field:
- `eq`: the displayed identity for every $j$.

*Meaning.* It is the local half of Siegel's theorem for the numbers $\rho\varpi^{2j}$ in the lattice $L_\mathfrak p$, in Weil's form "orbit
measure $\times$ stabilizer measure = constant": summing over the $O(L_\mathfrak p)$-orbits on $\{x \in L_\mathfrak p : Q(x) = \rho\varpi^{2j}\}$, the orbit of
$x$ has Leray measure $\mu(K)/\mu'(\mathrm{Stab}\,x)$ with Weil's gauge forms; the factors $|2\rho|^n$, $|\det g|^{-(n+1)}$ and $q^{j(n-1)}$ are the
Jacobians of the coordinates. **Proved** at every prime where the frame lattice is the standard lattice and $\mathrm{ord}\,\rho \le 1$
(`orbitalLocalIdentityAt_std`, dyadic primes included); an input at the finitely many other primes. *Independence:* one prime,
local densities and index ratios only; it does not mention classes, masses or $\tau$. -/
@[kb "weil1982" "§3.4 (local fibration) and §4.5, p. 109 (frame adapted to ξ_ρ) [unverified]"]
structure OrbitalLocalIdentityAt (Q₀ : QuadForm (𝓞 F) (n + 1)) {ρ : F} (fr : AdaptedFrame (formF Q₀) ρ) : Prop where
  eq : ∀ j : ℤ, locW v fr j * NF.siegelDensity v Q₀ Q₀ * ‖(2 : Fv) * algebraMap F Fv ρ‖ ^ n *
      (‖algebraMap F Fv fr.g.val.det‖ ^ (n + 1))⁻¹ =
    NF.siegelDensity v fr.Q' fr.Q' * (DVR.q 𝔬 : ℝ) ^ (j * ((n : ℤ) - 1)) *
      betaZ v Q₀ (algebraMap F Fv ρ * unifV v ^ (2 * j))

/-- **The standard primes of a frame**: the frame lattice is $\mathfrak o_\mathfrak p^{n+1}$ and $0 \le \mathrm{ord}_\mathfrak p\rho \le 1$. -/
def IsStdPrime {Q : QuadForm F (n + 1)} {ρ : F} (fr : AdaptedFrame Q ρ) : Prop :=
  frameLat v fr.g = std v ∧ Valued.v (algebraMap F Fv ρ) ≤ 1 ∧ WithZero.exp (-1 : ℤ) ≤ Valued.v (algebraMap F Fv ρ)

/-- An element of $\mathrm{GL}_N(F_\mathfrak p)$ stabilizing $\mathfrak o_\mathfrak p^N$ comes from $\mathrm{GL}_N(\mathfrak o_\mathfrak p)$. -/
theorem exists_GL_o_of_locAct_std {N : ℕ} (h : GL (Fin N) Fv) (hh : locAct v h (std v) = std v) :
    ∃ H : GL (Fin N) 𝔬, Matrix.GeneralLinearGroup.map (algebraMap 𝔬 Fv) H = h := by
  have hint : ∀ (k : GL (Fin N) Fv), locAct v k (std v) = std v → ∀ i j, Valued.v (k.val i j) ≤ 1 := by
    intro k hk i j
    have hmem : k.val *ᵥ (Pi.single j (1 : Fv)) ∈ std v := by
      rw [← hk]; exact ⟨_, single_one_mem_std v j, rfl⟩
    have := hmem i
    rw [neg_zero, WithZero.exp_zero] at this
    simpa [mulVec_single] using this
  have hh' : locAct v h⁻¹ (std v) = std v := by
    rw [locAct_eq_iff, inv_inv, hh]
  let A : Matrix (Fin N) (Fin N) 𝔬 := Matrix.of fun i j => toO v _ (hint h hh i j)
  let B : Matrix (Fin N) (Fin N) 𝔬 := Matrix.of fun i j => toO v _ (hint h⁻¹ hh' i j)
  have hA : A.map (algebraMap 𝔬 Fv) = h.val := by ext i j; rfl
  have hB : B.map (algebraMap 𝔬 Fv) = h⁻¹.val := by ext i j; rfl
  have hAB : A * B = 1 := map_o_injective v (by
    show (A * B).map _ = (1 : Matrix (Fin N) (Fin N) 𝔬).map _
    rw [Matrix.map_mul, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)])
  have hBA : B * A = 1 := map_o_injective v (by
    show (B * A).map _ = (1 : Matrix (Fin N) (Fin N) 𝔬).map _
    rw [Matrix.map_mul, hA, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)])
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

end LocalFrame

/-! #### Proof of the local identity at the standard primes -/

section LocalStd

open LocalDensity.DVR

theorem AdaptedFrame.nondegenerate {F : Type*} [Field F] [NumberField F] {n : ℕ} {Q : QuadForm F (n + 1)} {ρ : F}
    (fr : AdaptedFrame Q ρ) (hQ : Q.Nondegenerate) (hρ : ρ ≠ 0) : fr.Q'.Nondegenerate := by
  have h1 := congrArg (fun S : QuadForm F (n + 1) => S.hessian.det) fr.compMat_eq
  simp only [hessian_compMat, det_mul, det_transpose, det_hessian_splitForm] at h1
  have h2 : fr.g.val.det * Q.hessian.det * fr.g.val.det ≠ 0 :=
    mul_ne_zero (mul_ne_zero (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero hQ)
      (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
  rw [h1] at h2
  have h3 : (fr.Q'.map (algebraMap (𝓞 F) F)).hessian.det ≠ 0 := right_ne_zero_of_mul h2
  rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h3
  exact fun h => h3 (by rw [h, map_zero])

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {N : ℕ}

/-- **$r_{\pi^k}(m)$ depends only on the $\mathrm{GL}_N(R)$-class of $Q$**. -/
theorem repCount_congr_isometricGL {Q Q' : QuadForm R N} (h : Siegel.IsometricGL Q Q') (πR : R) (k : ℕ) (m : R) :
    LocalDensity.DVR.repCount Q πR k m = LocalDensity.DVR.repCount Q' πR k m := by
  obtain ⟨g, hg⟩ := h
  set f := Ideal.Quotient.mk (Ideal.span {πR ^ k})
  set gb := Matrix.GeneralLinearGroup.map f g
  have hQ' : Q'.map f = (Q.map f).compMat gb.val := by
    rw [← compMat_eq_of_isometricGL hg, ← map_compMat]; rfl
  unfold LocalDensity.DVR.repCount
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun := fun x => gb⁻¹.val *ᵥ x
      invFun := fun y => gb.val *ᵥ y
      left_inv := fun x => by
        simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      right_inv := fun y => by
        simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] } fun x => ?_)
  show _ ↔ Q'.evalIn _ (gb⁻¹.val *ᵥ x) = _
  rw [evalIn_eq_eval_map, evalIn_eq_eval_map, show (algebraMap R (R ⧸ Ideal.span {πR ^ k})) = f from rfl, hQ',
    eval_compMat, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem localDensity_congr_isometricGL [Finite (IsLocalRing.ResidueField R)] {Q Q' : QuadForm R N}
    (h : Siegel.IsometricGL Q Q') (πR m : R) :
    LocalDensity.DVR.localDensity Q πR m = LocalDensity.DVR.localDensity Q' πR m := by
  unfold LocalDensity.DVR.localDensity
  simp only [repCount_congr_isometricGL h]

end LocalStd

section LocalStdNF

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem norm_coe_of_pow_dvd {x : 𝔬} {e : ℕ} (he : NF.π v ^ e ∣ x) (he' : ¬ NF.π v ^ (e + 1) ∣ x) :
    ‖((x : 𝔬) : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ e)⁻¹ := by
  obtain ⟨u, rfl⟩ := he
  have hu : IsUnit u := by
    refine DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) fun h => he' ?_
    rw [pow_succ]; exact mul_dvd_mul_left _ h
  have hv : Valued.v (((NF.π v ^ e * u : 𝔬)) : Fv) = WithZero.exp (-(e : ℤ)) := by
    push_cast
    rw [map_mul, map_pow, NF.valued_π, (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hu,
      mul_one, ← WithZero.exp_nsmul]
    congr 1; simp
  have hx0 : ((NF.π v ^ e * u : 𝔬) : Fv) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.zero_ne_coe hv
  rw [LocalZeta.norm_eq_absNorm_pow v hx0, hv, WithZero.log_exp, NF.q_completion, _root_.zpow_neg, zpow_natCast]

theorem norm_coe_unit {u : 𝔬} (hu : IsUnit u) : ‖((u : 𝔬) : Fv)‖ = 1 := by
  have := norm_coe_of_pow_dvd v (e := 0) (x := u) (by simp) (by
    rw [zero_add, pow_one]; intro h; exact (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_unit h hu))
  rw [this, pow_zero, inv_one]

/-- **The local orbital identity at a standard prime** of the frame (Weil 1982, §3.4 [unverified]; every prime, dyadic
included): if $g^{-1}L_\mathfrak p = \mathfrak o_\mathfrak p^{n+1}$ and $0 \le \mathrm{ord}_\mathfrak p\rho \le 1$, `OrbitalLocalIdentityAt` holds. *Proof:* $g \in \mathrm{GL}_{n+1}(\mathfrak o_\mathfrak p)$, so
$Q_0 \cong \langle\rho\rangle\perp Q_0'$ over $\mathfrak o_\mathfrak p$ and the densities agree (`localDensityForm_congr_left/right`,
`localDensity_congr_isometricGL`), $|\det g|_\mathfrak p = 1$; for $j \ge 0$ this is `localIdentity_imprimitive`; for $j < 0$ both sides vanish
($\rho\varpi^{2j}$ is not integral, so neither the lattice nor any lattice of its genus contains $\varpi^je_0$). -/
@[kb "weil1982" "§3.4 (local fibration at the standard primes of the frame) [unverified]"]
theorem orbitalLocalIdentityAt_std (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ₀ : Q₀.Nondegenerate) (hn : 1 ≤ n) {ρ : F}
    (hρ : ρ ≠ 0) (fr : AdaptedFrame (formF Q₀) ρ) (hstd : IsStdPrime v fr) : OrbitalLocalIdentityAt v Q₀ fr := by
  classical
  obtain ⟨hlat, hρ1, hρ2⟩ := hstd
  set Q'o := fr.Q'
  set QF' := Q'o.map (algebraMap (𝓞 F) F)
  have hπ := NF.irreducible_π v
  have hQF : (formF Q₀).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ₀
  have hQ'nd : Q'o.Nondegenerate := fr.nondegenerate hQF hρ
  -- `g` is integral at `v`
  set gv := Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g
  have hstdg : locAct v gv⁻¹ (std v) = std v := by
    have := hlat
    rw [frameLat, loc_glImage, loc_intVec, map_inv] at this
    exact this
  obtain ⟨Hi, hHi⟩ := exists_GL_o_of_locAct_std v gv⁻¹ hstdg
  set H := Hi⁻¹
  have hH : Matrix.GeneralLinearGroup.map (algebraMap 𝔬 Fv) H = gv := by
    rw [map_inv, hHi, inv_inv]
  have hHval : H.val.map (algebraMap 𝔬 Fv) = fr.g.val.map (algebraMap F Fv) := by
    have := congrArg Units.val hH
    exact this
  -- the integral model of the split form
  set ρo : 𝔬 := toO v _ hρ1
  have hmoF : ((ρo : 𝔬) : Fv) = algebraMap F Fv ρ := rfl
  have hQo' : IsIntModel v QF' (NF.Qp v Q'o) := fun y => evalIn_coe_o v Q'o y
  set Qs := splitForm ρo (NF.Qp v Q'o)
  have hQs : IsIntModel v (splitForm ρ QF') Qs := isIntModel_splitForm v ρ QF' hQo' hmoF
  have hiso : Siegel.IsometricGL (NF.Qp v Q₀) Qs := by
    refine ⟨H, fun x => Subtype.ext ?_⟩
    show (((NF.Qp v Q₀).eval (H.val *ᵥ x) : 𝔬) : Fv) = ((Qs.eval x : 𝔬) : Fv)
    rw [← evalIn_coe_o v Q₀, coe_mulVec_o, hHval, ← hQs, ← fr.compMat_eq, evalIn_compMat_gl]
  have hα : NF.siegelDensity v Q₀ Q₀ = 1 / 2 * DVR.localDensityForm Qs Qs (NF.π v) := by
    unfold NF.siegelDensity
    rw [if_pos rfl, NF.localDensityForm_eq_completion, DVR.localDensityForm_congr_left hiso,
      DVR.localDensityForm_congr_right Qs hiso]
  have hα' : NF.siegelDensity v Q'o Q'o = 1 / 2 * DVR.localDensityForm (NF.Qp v Q'o) (NF.Qp v Q'o) (NF.π v) := by
    unfold NF.siegelDensity
    rw [if_pos rfl, NF.localDensityForm_eq_completion]
  have hdet : ‖algebraMap F Fv fr.g.val.det‖ = 1 := by
    have e1 : algebraMap F Fv fr.g.val.det = ((H.val.det : 𝔬) : Fv) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hHval, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rfl
    rw [e1]
    exact norm_coe_unit v (H.isUnit.map Matrix.detMonoidHom)
  have hval_unif : ∀ k : ℤ, Valued.v (unifV v ^ k) = WithZero.exp (-k) := by
    intro k
    rw [map_zpow₀, NF.valued_π, ← WithZero.exp_zsmul]
    congr 1; simp
  refine ⟨fun j => ?_⟩
  rcases lt_or_ge j 0 with hj | hj
  · -- `j < 0`: both sides vanish
    have hbig : ¬ Valued.v (algebraMap F Fv ρ * unifV v ^ (2 * j)) ≤ 1 := by
      rw [map_mul, hval_unif]
      intro hle
      have h1 : WithZero.exp (-1 : ℤ) * WithZero.exp (-(2 * j)) ≤ 1 :=
        (mul_le_mul' hρ2 le_rfl).trans hle
      rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
      omega
    have hW : locW v fr j = 0 := by
      have hE : IsEmpty (LocCompSetG v ρ QF' (frameLat v fr.g) (unifV v ^ j)) := by
        refine ⟨fun M => ?_⟩
        obtain ⟨g', hg'⟩ := M.2.1
        have hm := M.2.2
        rw [← hg', hlat] at hm
        obtain ⟨y, hy, hgy⟩ := hm
        replace hgy : (g' : GL (Fin (n + 1)) Fv).val *ᵥ y = unifV v ^ j • (e₀ : Fin (n + 1) → Fv) := hgy
        obtain ⟨y', rfl⟩ := integral_of_mem_std v hy
        have hval : (splitForm ρ QF').evalIn Fv (fun i => (y' i : Fv)) =
            (unifV v ^ j) ^ 2 * algebraMap F Fv ρ := by
          rw [← evalIn_mulVec_of_mem _ g'.2, hgy, evalIn_smul', evalIn_splitForm_e₀]
        rw [hQs] at hval
        apply hbig
        have hle : Valued.v (((Qs.eval y' : 𝔬)) : Fv) ≤ 1 :=
          (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (Qs.eval y').2
        rw [hval] at hle
        convert hle using 2
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, Nat.cast_ofNat, mul_comm (2 : ℤ)]
      have hE' : IsEmpty (LocTypesG v ρ QF' (frameLat v fr.g) (unifV v ^ j)) :=
        ⟨fun t => hE.false t.out⟩
      unfold locW
      rw [locTypeSumG, finsum_of_isEmpty]
    have hβ : betaZ v Q₀ (algebraMap F Fv ρ * unifV v ^ (2 * j)) = 0 := by
      unfold betaZ; rw [dif_neg hbig]
    rw [hW, hβ]; ring
  · -- `j ≥ 0`: the imprimitive identity
    obtain ⟨j', rfl⟩ := Int.eq_ofNat_of_zero_le hj
    have h2ρ0 : (2 * ρo : 𝔬) ≠ 0 := by
      refine mul_ne_zero (NF.two_ne_zero' v) fun h0 => hρ ?_
      have : algebraMap F Fv ρ = 0 := by rw [← hmoF, h0]; rfl
      exact (map_eq_zero_iff _ (algebraMap F Fv).injective).mp this
    obtain ⟨e, he, he'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ h2ρ0
    have hid := localIdentity_imprimitive v Q'o hQ'nd hn hρ hmoF j' he he'
    have hW : locW v fr (j' : ℤ) = locTypeSumG v ρ QF' (std v) (((NF.π v ^ j' : 𝔬) : Fv)) := by
      unfold locW; rw [hlat, zpow_natCast]; push_cast; rfl
    have h2ρ : ‖(2 : Fv) * algebraMap F Fv ρ‖ = ((DVR.q 𝔬 : ℝ) ^ e)⁻¹ := by
      rw [← norm_coe_of_pow_dvd v he he']
      push_cast; rfl
    have hint : Valued.v (algebraMap F Fv ρ * unifV v ^ (2 * (j' : ℤ))) ≤ 1 := by
      rw [map_mul]
      have : Valued.v (unifV v ^ (2 * (j' : ℤ))) ≤ 1 := by
        rw [hval_unif, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
      calc Valued.v (algebraMap F Fv ρ) * Valued.v (unifV v ^ (2 * (j' : ℤ))) ≤ 1 * 1 :=
            mul_le_mul' hρ1 this
        _ = 1 := one_mul 1
    have hβ : betaZ v Q₀ (algebraMap F Fv ρ * unifV v ^ (2 * (j' : ℤ))) =
        DVR.localDensity Qs (NF.π v) (NF.π v ^ (2 * j') * ρo) := by
      unfold betaZ
      rw [dif_pos hint, ← localDensity_congr_isometricGL hiso]
      congr 1
      apply Subtype.ext
      show algebraMap F Fv ρ * unifV v ^ (2 * (j' : ℤ)) = ((NF.π v ^ (2 * j') * ρo : 𝔬) : Fv)
      push_cast
      rw [← hmoF, mul_comm, show (2 * (j' : ℤ)) = ((2 * j' : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    have hexp : ((j' : ℤ) * ((n : ℤ) - 1)) = ((j' * (n - 1) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hn]; ring
    rw [hW, hα, hα', h2ρ, hdet, hβ, hexp, zpow_natCast, one_pow, inv_one, mul_one]
    have hq : (0 : ℝ) < DVR.q 𝔬 := Nat.cast_pos.mpr (DVR.q_pos (R := 𝔬))
    have hqe : ((DVR.q 𝔬 : ℝ) ^ e) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hq.ne')
    rw [inv_pow]
    field_simp
    rw [hid, ← pow_mul]

end LocalStdNF

/-! ### Steps 2–3: the genus count of $\beta^2\rho$ as a product of local type sums -/

section PerIdeal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- $D_\beta = \mathrm{diag}(\beta, 1, \dots, 1) \in \mathrm{GL}_{n+1}(F)$. -/
def diagGl {β : F} (hβ : β ≠ 0) : GL (Fin (n + 1)) F :=
  ⟨cornerMat β 1, cornerMat β⁻¹ 1, by rw [cornerMat_mul, mul_inv_cancel₀ hβ, Matrix.one_mul, cornerMat_one],
    by rw [cornerMat_mul, inv_mul_cancel₀ hβ, Matrix.one_mul, cornerMat_one]⟩

theorem splitForm_compMat_cornerMat (ρ β : F) (Q' : QuadForm F n) :
    (splitForm ρ Q').compMat (cornerMat β 1) = splitForm (β ^ 2 * ρ) Q' := by
  refine eq_of_eval_eq fun x => ?_
  rw [eval_compMat, ← Fin.cons_self_tail x, cornerMat_mulVec, Matrix.one_mulVec, eval_splitForm_cons,
    eval_splitForm_cons]
  ring

theorem map_diagGl (v : HeightOneSpectrum (𝓞 F)) {β : F} (hβ : β ≠ 0)
    (hβv : algebraMap F (v.adicCompletion F) β ≠ 0) :
    Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (diagGl (n := n) hβ) = diagD v hβv := by
  ext1
  show (cornerMat β 1).map _ = cornerMat _ 1
  rw [cornerMat_map, Matrix.map_one _ (map_zero _) (map_one _)]

/-- **Steps 2–3: the genus count of $\beta^2\rho$ factors over the primes** (Weil 1982, §4.5, p. 109; §3.4–3.5 [unverified locator]): for
$Q_0$ totally positive definite, an adapted frame $Q_0\circ g = \langle\rho\rangle\perp Q_0'$ and $\beta \in F^\times$,
$$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}\,\mathcal O_F^{n+1}}\frac{r_M(\beta^2\rho)}{|O(M)|} = \mathrm{Mass}(Q_0')\prod_\mathfrak pW_\mathfrak p(g^{-1}L_\mathfrak p, \beta).$$
*Proof:* change coordinates by $g\,D_\beta$ (`repMass_compMat`), so that $Q = \langle\beta^2\rho\rangle\perp Q_0'$; `repMass_eq_mass_mul`;
the factorization `typeSum_eq_prodG`; transport each local factor back along $D_\beta$ (`locTypeSumG_transport`); the
factors off the exceptional set are $1$ (`locTypeSumG_std_eq_one`). -/
@[kb "weil1982" "§4.5, p. 109 (orbit counting in coordinates adapted to ξ_ρ); §3.4-3.5 [unverified locator]"]
theorem repMass_eq_mass_mul_finprod (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    {ρ : F} (hρ : ρ ≠ 0) (fr : AdaptedFrame (formF Q₀) ρ) {β : F} (hβ : β ≠ 0) :
    repMass (formF Q₀) (stdLat F (n + 1)) (β ^ 2 * ρ) =
      mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F n) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 F),
          locTypeSumG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) (algebraMap F (v.adicCompletion F) β) := by
  classical
  set QF' := fr.Q'.map (algebraMap (𝓞 F) F)
  set gb : GL (Fin (n + 1)) F := fr.g * diagGl hβ
  set m := β ^ 2 * ρ
  have hm : m ≠ 0 := mul_ne_zero (pow_ne_zero 2 hβ) hρ
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  have hQF' : QF'.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ'nd
  have hcomp : (formF Q₀).compMat gb.val = splitForm m QF' := by
    rw [show gb.val = fr.g.val * cornerMat β 1 from rfl, ← compMat_mul, fr.compMat_eq,
      splitForm_compMat_cornerMat]
  have hLi₀ : Lattices.IsIntegral (formF Q₀) (stdLat F (n + 1)).1 := HilbertModular.isIntegral_stdLat Q₀
  set Λ := Lat.image gb⁻¹ (stdLat F (n + 1))
  have hpd_s : IsTotallyPosDef (splitForm m QF') := hcomp ▸ isTotallyPosDef_compMat (formF Q₀) gb hpd
  have hLi_s : Lattices.IsIntegral (splitForm m QF') Λ.1 := hcomp ▸ isIntegral_compMat (formF Q₀) gb hLi₀
  have hLi' : Lattices.IsIntegral QF' (stdLat F n).1 := HilbertModular.isIntegral_stdLat fr.Q'
  have hpd' := isTotallyPosDef_of_splitForm hpd_s
  rw [← repMass_compMat (formF Q₀) gb hpd hLi₀ m, hcomp, repMass_eq_mass_mul m QF' Λ hpd_s hLi_s hm hpd' hLi',
    typeSum_eq_prodG m fr.Q' Λ hm hQ'nd hpd_s hLi_s hLi']
  congr 1
  -- the local factors in the frame coordinates
  set T : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    locTypeSumG v ρ QF' (frameLat v fr.g) (algebraMap F (v.adicCompletion F) β)
  have hβv : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) β ≠ 0 :=
    fun v => (map_ne_zero _).mpr hβ
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      locTypeSumG v m QF' (loc v Λ.1) 1 = T v := by
    intro v
    have hΛ : (loc v Λ.1).IsLattice (v.adicCompletion F) := loc_isLattice v Λ.2
    rw [locTypeSumG_transport v QF' hQF' ρ (hβv v) (by simp only [m, map_mul, map_pow]; ring) hΛ 1, mul_one]
    congr 1
    show locAct v (diagD v (hβv v)) (loc v (glImage gb⁻¹ intVec)) = loc v (glImage fr.g⁻¹ intVec)
    rw [loc_glImage, loc_glImage, loc_intVec, ← locAct_mul, show gb⁻¹ = (diagGl hβ)⁻¹ * fr.g⁻¹ by
      simp [gb, _root_.mul_inv_rev], map_mul, map_inv, map_diagGl v hβ (hβv v), ← mul_assoc, mul_inv_cancel, one_mul]
  have hone : ∀ v ∉ badSetG m Λ hm, T v = 1 := by
    intro v hv
    obtain ⟨hL, hmv, h2v⟩ := not_mem_badSetG m Λ hm hv
    rw [← hloc v, hL]
    have hmv' : Valued.v (algebraMap F (v.adicCompletion F) m) ≤ 1 := by rw [valued_algebraMap, hmv]
    set mo := toO v _ hmv'
    have hmo : ((mo : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F _ m := rfl
    have hQo' : IsIntModel v QF' (NF.Qp v fr.Q') := fun y => evalIn_coe_o v fr.Q' y
    have hunit : ∀ x : v.adicCompletionIntegers F, Valued.v (x : v.adicCompletion F) = 1 → IsUnit x := by
      intro x hx
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      exact hx
    have h2u : IsUnit (2 : v.adicCompletionIntegers F) := by
      apply hunit
      have : ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F _ 2 := by
        rw [map_ofNat]; rfl
      rw [this, valued_algebraMap, h2v]
    have hmu : IsUnit mo := hunit mo (by rw [hmo, valued_algebraMap, hmv])
    have h4 : IsUnit (4 * mo) := by
      rw [show (4 : v.adicCompletionIntegers F) = 2 * 2 by norm_num]
      exact (h2u.mul h2u).mul hmu
    have hnd : (splitForm mo (NF.Qp v fr.Q')).Nondegenerate := by
      rw [QuadForm.Nondegenerate, det_hessian_splitForm]
      exact mul_ne_zero (mul_ne_zero (NF.two_ne_zero' v) hmu.ne_zero) (NF.nondegenerate_Qp v hQ'nd)
    exact locTypeSumG_std_eq_one v m QF' hQF' hQo' hmo h4 hnd
  rw [Finset.prod_congr rfl fun v _ => hloc v]
  exact (finprod_eq_prod_of_mulSupport_subset T fun v hv => by
    by_contra h; exact hv (hone v h)).symm

end PerIdeal

/-! ### The local series $\sum_jN\mathfrak p^{-j(N+2s)}W_\mathfrak p(j)$ -/

section LocalSeries

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

open FractionalIdeal in
/-- $|\beta|_\mathfrak p = \exp(-\mathrm{ord}_\mathfrak p(\beta))$ with $\mathrm{ord}_\mathfrak p(\beta) = $ `count` of the principal ideal $(\beta)$. -/
theorem valued_eq_exp_neg_count {β : F} (hβ : β ≠ 0) :
    Valued.v (algebraMap F Fv β) = WithZero.exp (-count F v (spanSingleton (𝓞 F)⁰ β)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) β
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hβ
  have hbF : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hb0
  have hspan : spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) =
      spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F) b)⁻¹ * ↑(Ideal.span {a}) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, div_eq_mul_inv, mul_comm]
  have hne : spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) ≠ 0 :=
    spanSingleton_ne_zero_iff.mpr hβ
  rw [count_well_defined F v hne hspan, valued_algebraMap, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, v.intValuation_if_neg ha0, v.intValuation_if_neg hb0,
    ← WithZero.exp_sub]
  congr 1
  ring

theorem locTypeSumG_nonneg {m : F} {n' : ℕ} {Q' : QuadForm F n'} {Λ : Submodule 𝔬 (Fin (n' + 1) → Fv)} {c : Fv} :
    0 ≤ locTypeSumG v m Q' Λ c :=
  finsum_nonneg fun t => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

open FractionalIdeal in
/-- **The frame factor of $\beta$ is $W_\mathfrak p(\mathrm{ord}_\mathfrak p\beta)$** (`locTypeSumG_unit`: $\beta = u\varpi^{\mathrm{ord}\beta}$). -/
theorem locTypeSumG_frame_eq_locW {Q : QuadForm F (n + 1)} {ρ : F} (fr : AdaptedFrame Q ρ) (hQ' : fr.Q'.Nondegenerate)
    {β : F} (hβ : β ≠ 0) :
    locTypeSumG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) (algebraMap F Fv β) =
      locW v fr (count F v (spanSingleton (𝓞 F)⁰ β)) := by
  set j := count F v (spanSingleton (𝓞 F)⁰ β)
  have hQF' : (fr.Q'.map (algebraMap (𝓞 F) F)).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ'
  have hvϖ : Valued.v (unifV v) = WithZero.exp (-1 : ℤ) := NF.valued_π v
  have hϖ0 : unifV v ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hval : Valued.v (algebraMap F Fv β * unifV v ^ (-j)) = 1 := by
    rw [map_mul, valued_eq_exp_neg_count v hβ, map_zpow₀, hvϖ, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      show -j + (-j) • (-1 : ℤ) = 0 by simp, WithZero.exp_zero]
  set u : 𝔬 := toO v _ hval.le
  have hu : IsUnit u := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]; exact hval
  have hβu : algebraMap F Fv β = (u : Fv) * unifV v ^ j := by
    show algebraMap F Fv β = (algebraMap F Fv β * unifV v ^ (-j)) * unifV v ^ j
    rw [mul_assoc, ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, mul_one]
  have hΛ : (frameLat v fr.g).IsLattice Fv := loc_isLattice v (glImage_isLattice _ intVec_isLattice)
  rw [hβu, show ((u : 𝔬) : Fv) = ((hu.unit : 𝔬ˣ) : 𝔬) from rfl,
    locTypeSumG_unit v ρ _ hQF' hΛ (unifV v ^ j) hu.unit]
  rfl

/-- **Positivity of $\alpha_\mathfrak p(L, L)$**: $A_{\mathfrak p^k}(L, L) \ge 1$ (the identity), and $\alpha_\mathfrak p = A_{\mathfrak p^k}/N\mathfrak p^{ke}$ for large $k$. -/
theorem siegelDensity_pos {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) :
    0 < NF.siegelDensity v Q₀ Q₀ := by
  obtain ⟨k, hk⟩ := (NF.localDensityForm_eventually_eq v Q₀ Q₀ hQ le_rfl).exists
  unfold NF.siegelDensity
  rw [if_pos rfl, ← hk]
  have : Finite (𝓞 F ⧸ v.asIdeal ^ k) :=
    Ideal.finiteQuotientOfFreeOfNeBot (v.asIdeal ^ k) (pow_ne_zero _ v.ne_bot)
  have : Nonempty {X : Matrix (Fin N) (Fin N) (𝓞 F ⧸ v.asIdeal ^ k) //
      (Q₀.map (Ideal.Quotient.mk _)).compMat X = Q₀.map (Ideal.Quotient.mk _)} := ⟨⟨1, compMat_one _⟩⟩
  have hpos : 0 < NF.repCountForm v Q₀ Q₀ k := Nat.card_pos
  have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot))
  have : (0 : ℝ) < NF.repCountForm v Q₀ Q₀ k := by exact_mod_cast hpos
  positivity

/-- **The local spherical factor as a series over $\mathbb Z$** (`hasSum_levelTerm`, reindexed by $l = \mathrm{ord}\,\rho + 2j$):
$$\sum_{j\in\mathbb Z}|\varpi^{2j}|^{1+s}\,\beta_\mathfrak p(\rho\varpi^{2j}) = |\rho|^{-(1+s)}\,|2|^{-1}\,Z_\mathfrak p(s,\rho).$$ -/
theorem hasSum_betaZ_series {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (hN : 1 ≤ N) {ρ : Fv}
    (hρ : ρ ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    HasSum (fun j : ℤ => ‖unifV v ^ (2 * j)‖ ^ (1 + s) * betaZ v Q₀ (ρ * unifV v ^ (2 * j)))
      (‖ρ‖ ^ (-(1 + s)) * (‖(2 : Fv)‖⁻¹ * QuadFormsKB.SphericalZeta.sphLocal Q₀ v ρ s)) := by
  classical
  have hL := QuadFormsKB.SphericalLocalFactor.hasSum_levelTerm v Q₀ hQ hN hρ hs
  set ord := QuadFormsKB.SphericalLocalFactor.ordF v ρ
  set B : ℤ → ℝ := fun l => if 0 ≤ l then QuadFormsKB.SphericalLocalFactor.levelTerm v (NF.Qp v Q₀) hρ s l.toNat else 0
  have hB : HasSum B (‖(2 : Fv)‖⁻¹ * QuadFormsKB.SphericalZeta.sphLocal Q₀ v ρ s) := by
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff (f := B)]
    · convert hL using 1
      funext l
      simp [B]
    · intro l hl
      simp only [B]
      rw [if_neg]
      intro h0
      exact hl ⟨l.toNat, Int.toNat_of_nonneg h0⟩
  set e : ℤ → ℤ := fun j => ord + 2 * j
  have he : Function.Injective e := fun a b h => by simp only [e] at h; omega
  have hBe : HasSum (B ∘ e) (‖(2 : Fv)‖⁻¹ * QuadFormsKB.SphericalZeta.sphLocal Q₀ v ρ s) := by
    rw [he.hasSum_iff]
    · exact hB
    · intro l hl
      simp only [B]
      split_ifs with h0
      · unfold QuadFormsKB.SphericalLocalFactor.levelTerm
        rw [if_neg]
        rintro ⟨m, hm⟩
        apply hl
        refine ⟨m, ?_⟩
        simp only [e]
        rw [Int.toNat_of_nonneg h0] at hm
        omega
      · rfl
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hϖ0 : unifV v ≠ 0 := by
    have hvϖ : Valued.v (unifV v) = WithZero.exp (-1 : ℤ) := NF.valued_π v
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  refine (hBe.mul_left (‖ρ‖ ^ (-(1 + s)))).congr_fun fun j => ?_
  simp only [Function.comp_apply, B, e]
  have hvt : Valued.v (ρ * unifV v ^ (2 * j)) = WithZero.exp (-(ord + 2 * j)) := by
    rw [map_mul, map_zpow₀, NF.valued_π, ← WithZero.exp_zsmul, ← WithZero.exp_log ((Valued.v).ne_zero_iff.mpr hρ),
      ← WithZero.exp_add]
    congr 1
    simp only [ord, QuadFormsKB.SphericalLocalFactor.ordF, smul_eq_mul]
    ring
  split_ifs with h0
  · have hl : ((ord + 2 * j).toNat : ℤ) - ord = 2 * j := by rw [Int.toNat_of_nonneg h0]; ring
    have hev : Even (((ord + 2 * j).toNat : ℤ) - ord) := by rw [hl]; exact even_two_mul j
    unfold QuadFormsKB.SphericalLocalFactor.levelTerm
    rw [if_pos hev]
    have htl : QuadFormsKB.SphericalLocalFactor.tLev v ρ (ord + 2 * j).toNat = ρ * unifV v ^ (2 * j) := by
      unfold QuadFormsKB.SphericalLocalFactor.tLev; rw [hl]
    have hle : Valued.v (ρ * unifV v ^ (2 * j)) ≤ 1 := by
      rw [hvt, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    unfold betaZ
    rw [dif_pos hle, htl, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ← mul_assoc,
      ← mul_assoc, ← Real.rpow_add hρn, show -(1 + s) + (1 + s) = (0 : ℝ) by ring, Real.rpow_zero, one_mul]
    congr 2
    apply Subtype.ext
    rw [QuadFormsKB.SphericalLocalFactor.coe_tLevO, htl]
  · have hle : ¬ Valued.v (ρ * unifV v ^ (2 * j)) ≤ 1 := by
      rw [hvt, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    unfold betaZ
    rw [dif_neg hle]
    ring

theorem norm_unifV_zpow (k : ℤ) : ‖unifV v ^ k‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
  have hvϖ : Valued.v (unifV v) = WithZero.exp (-1 : ℤ) := NF.valued_π v
  have hϖ0 : unifV v ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  rw [LocalZeta.norm_eq_absNorm_pow v (zpow_ne_zero k hϖ0), map_zpow₀, hvϖ, ← WithZero.exp_zsmul,
    WithZero.log_exp]
  congr 1; simp

/-- **The local series of the frame** (from the local identity at $\mathfrak p$): with $q = N\mathfrak p$,
$$\sum_{j\in\mathbb Z}q^{-j(n+1+2s)}W_\mathfrak p(j) = \frac{\alpha_\mathfrak p(Q_0')\,|\det g|^{n+1}}{\alpha_\mathfrak p(Q_0)\,|2\rho|^n}\,|\rho|^{-(1+s)}\,|2|^{-1}\,Z_\mathfrak p(s,\rho).$$ -/
theorem hasSum_locW (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ₀ : Q₀.Nondegenerate) {ρ : F} (hρ : ρ ≠ 0)
    (fr : AdaptedFrame (formF Q₀) ρ) (hgli : OrbitalLocalIdentityAt v Q₀ fr) {s : ℝ} (hs : 0 ≤ s) :
    HasSum (fun j : ℤ => ((Ideal.absNorm v.asIdeal : ℝ) ^ j) ^ (-((n + 1 : ℕ) + 2 * s)) * locW v fr j)
      (NF.siegelDensity v fr.Q' fr.Q' * ‖algebraMap F Fv fr.g.val.det‖ ^ (n + 1) /
          (NF.siegelDensity v Q₀ Q₀ * ‖(2 : Fv) * algebraMap F Fv ρ‖ ^ n) *
        (‖algebraMap F Fv ρ‖ ^ (-(1 + s)) * (‖(2 : Fv)‖⁻¹ * QuadFormsKB.SphericalZeta.sphLocal Q₀ v
          (algebraMap F Fv ρ) s))) := by
  have hρv : algebraMap F Fv ρ ≠ 0 := (map_ne_zero _).mpr hρ
  have hS := hasSum_betaZ_series v Q₀ hQ₀ (by omega) hρv hs
  have hα := siegelDensity_pos v Q₀ hQ₀
  have hA : 0 < ‖(2 : Fv) * algebraMap F Fv ρ‖ ^ n :=
    pow_pos (norm_pos_iff.mpr (mul_ne_zero two_ne_zero hρv)) n
  have hdet0 : algebraMap F Fv fr.g.val.det ≠ 0 :=
    (map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
  have hB : 0 < ‖algebraMap F Fv fr.g.val.det‖ ^ (n + 1) := pow_pos (norm_pos_iff.mpr hdet0) _
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot))
  set K := NF.siegelDensity v fr.Q' fr.Q' * ‖algebraMap F Fv fr.g.val.det‖ ^ (n + 1) /
    (NF.siegelDensity v Q₀ Q₀ * ‖(2 : Fv) * algebraMap F Fv ρ‖ ^ n)
  refine (hS.mul_left K).congr_fun fun j => ?_
  have hj := hgli.eq j
  have hqn : (DVR.q 𝔬 : ℝ) = Ideal.absNorm v.asIdeal := by rw [NF.q_completion]
  rw [hqn] at hj
  -- `W = K q^{j(n-1)} β`
  have hW : locW v fr j = K * ((Ideal.absNorm v.asIdeal : ℝ) ^ (j * ((n : ℤ) - 1)) *
      betaZ v Q₀ (algebraMap F Fv ρ * unifV v ^ (2 * j))) := by
    have hαA : NF.siegelDensity v Q₀ Q₀ * ‖(2 : Fv) * algebraMap F Fv ρ‖ ^ n ≠ 0 := by positivity
    calc locW v fr j = (locW v fr j * NF.siegelDensity v Q₀ Q₀ * ‖(2 : Fv) * algebraMap F Fv ρ‖ ^ n *
          (‖algebraMap F Fv fr.g.val.det‖ ^ (n + 1))⁻¹) * ‖algebraMap F Fv fr.g.val.det‖ ^ (n + 1) /
            (NF.siegelDensity v Q₀ Q₀ * ‖(2 : Fv) * algebraMap F Fv ρ‖ ^ n) := by
          field_simp
      _ = _ := by rw [hj]; simp only [K]; ring
  rw [hW, norm_unifV_zpow]
  -- the powers of `q`
  have hpow : ((Ideal.absNorm v.asIdeal : ℝ) ^ j) ^ (-((n + 1 : ℕ) + 2 * s)) *
      (Ideal.absNorm v.asIdeal : ℝ) ^ (j * ((n : ℤ) - 1)) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 * j))) ^ (1 + s) := by
    rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le,
      ← Real.rpow_mul hq.le, ← Real.rpow_add hq]
    congr 1
    push_cast
    ring
  rw [← hpow]
  ring

end LocalSeries

/-! ### $\prod_\mathfrak p\alpha_\mathfrak p(L, L) > 0$ -/

section ProdPos

variable {F : Type} [Field F] [NumberField F]

/-- **$\prod_\mathfrak p\alpha_\mathfrak p(L, L) > 0$** in every rank $N \ge 3$: the value of the convergent product is a finite product of positive
local factors times inverses of $\zeta_F(2i) \ge 1$ (and of $L(m,\chi) > 0$ in even rank) (`hasProd_siegelDensity_odd/even`). -/
theorem tprod_siegelDensity_pos {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) :
    0 < ∏' v, NF.siegelDensity v Q₀ Q₀ := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · rw [(hasProd_siegelDensity_even m (by omega) Q₀ hQ).tprod_eq]
    refine mul_pos (Finset.prod_pos fun v _ => div_pos (siegelDensity_pos v Q₀ hQ) (genericEven_pos Q₀ m (by omega) v))
      (mul_pos (inv_pos.mpr (NFEuler.LFunctionNF_pos (fun v => abs_chiP_le Q₀ v) (by
        have : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
        linarith))) (Finset.prod_pos fun i _ => inv_pos.mpr ?_))
    exact lt_of_lt_of_le one_pos (NFEuler.one_le_dedekindZetaR (by
      have : (2 : ℝ) ≤ ((2 * (i + 1) : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * (i + 1) by omega)
      linarith))
  · rw [(hasProd_siegelDensity_odd m Q₀ hQ).tprod_eq]
    refine mul_pos (Finset.prod_pos fun v _ => div_pos (siegelDensity_pos v Q₀ hQ) (genericOdd_pos m v))
      (Finset.prod_pos fun i _ => inv_pos.mpr ?_)
    exact lt_of_lt_of_le one_pos (NFEuler.one_le_dedekindZetaR (by
      have : (2 : ℝ) ≤ ((2 * (i + 1) : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * (i + 1) by omega)
      linarith))

end ProdPos

/-! ### Step 5: the orbital series as an Euler product -/

section Euler

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- One local type of weight $1$ at the standard lattice when $m$ and $2$ are $\mathfrak p$-units. -/
theorem locTypeSumG_std_one_of_units (v : HeightOneSpectrum (𝓞 F)) (Q₀' : QuadForm (𝓞 F) n)
    (hQ' : Q₀'.Nondegenerate) {m : F} (hmv : v.valuation F m = 1) (h2v : v.valuation F 2 = 1) :
    locTypeSumG v m (Q₀'.map (algebraMap (𝓞 F) F)) (std v) 1 = 1 := by
  have hQF' : (Q₀'.map (algebraMap (𝓞 F) F)).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ'
  have hmv' : Valued.v (algebraMap F (v.adicCompletion F) m) ≤ 1 := by rw [valued_algebraMap, hmv]
  set mo := toO v _ hmv'
  have hmo : ((mo : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F _ m := rfl
  have hQo' : IsIntModel v (Q₀'.map (algebraMap (𝓞 F) F)) (NF.Qp v Q₀') := fun y => evalIn_coe_o v Q₀' y
  have hunit : ∀ x : v.adicCompletionIntegers F, Valued.v (x : v.adicCompletion F) = 1 → IsUnit x := by
    intro x hx
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hx
  have h2u : IsUnit (2 : v.adicCompletionIntegers F) := by
    apply hunit
    have : ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F _ 2 := by
      rw [map_ofNat]; rfl
    rw [this, valued_algebraMap, h2v]
  have hmu : IsUnit mo := hunit mo (by rw [hmo, valued_algebraMap, hmv])
  have h4 : IsUnit (4 * mo) := by
    rw [show (4 : v.adicCompletionIntegers F) = 2 * 2 by norm_num]
    exact (h2u.mul h2u).mul hmu
  have hnd : (splitForm mo (NF.Qp v Q₀')).Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]
    exact mul_ne_zero (mul_ne_zero (NF.two_ne_zero' v) hmu.ne_zero) (NF.nondegenerate_Qp v hQ')
  exact locTypeSumG_std_eq_one v m _ hQF' hQo' hmo h4 hnd

/-- The frame's finite-place correction factor $D_\mathfrak p = |\det g|_\mathfrak p^{n+1}|2\rho|_\mathfrak p^{-n}|\rho|_\mathfrak p^{-(1+s)}|2|_\mathfrak p^{-1}$ ($= 1$ at almost all $\mathfrak p$). -/
def frameD {Q : QuadForm F (n + 1)} {ρ : F} (fr : AdaptedFrame Q ρ) (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n + 1) /
      ‖(2 : v.adicCompletion F) * algebraMap F (v.adicCompletion F) ρ‖ ^ n *
    (‖algebraMap F (v.adicCompletion F) ρ‖ ^ (-(1 + s)) * ‖(2 : v.adicCompletion F)‖⁻¹)

theorem norm_algebraMap_eq_one {v : HeightOneSpectrum (𝓞 F)} {x : F} (hx : v.valuation F x = 1) :
    ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  have hx0 : algebraMap F (v.adicCompletion F) x ≠ 0 := by
    intro h; rw [map_eq_zero_iff _ (algebraMap F _).injective] at h; rw [h, map_zero] at hx; exact zero_ne_one hx
  rw [LocalZeta.norm_eq_absNorm_pow v hx0, valued_algebraMap, hx, WithZero.log_one, zpow_zero]

theorem frameD_eq_one {Q : QuadForm F (n + 1)} {ρ : F} (fr : AdaptedFrame Q ρ) (s : ℝ) {v : HeightOneSpectrum (𝓞 F)}
    (hdet : v.valuation F fr.g.val.det = 1) (hρ : v.valuation F ρ = 1) (h2 : v.valuation F 2 = 1) :
    frameD fr s v = 1 := by
  have h2' : ‖(2 : v.adicCompletion F)‖ = 1 := by
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2]; exact norm_algebraMap_eq_one h2
  simp only [frameD, norm_mul, h2', norm_algebraMap_eq_one hdet, norm_algebraMap_eq_one hρ, one_pow, one_mul,
    Real.one_rpow, inv_one, div_one]

theorem finite_frameD_ne_one {Q : QuadForm F (n + 1)} {ρ : F} (fr : AdaptedFrame Q ρ) (hρ : ρ ≠ 0) (s : ℝ) :
    {v : HeightOneSpectrum (𝓞 F) | frameD fr s v ≠ 1}.Finite := by
  have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
  refine ((finite_valuation_ne_one hdet).union ((finite_valuation_ne_one hρ).union
    (finite_valuation_ne_one (two_ne_zero (α := F))))).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
  exact hv (frameD_eq_one fr s h.1 h.2.1 h.2.2)

theorem latClass_repCount_eq {N : ℕ} (Q : QuadForm F N) (c : LatClass Q) (t : F) :
    LatClass.repCount Q c t = repCount Q c.out t := by
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

/-- **Step 1 summed over the classes**: $\sum_{\mathrm{cls}M}\#\{\eta\in\mathfrak b^{-1}M : Q(\eta) = \rho\}/|O(M)| = \mathrm{repMass}(\beta^2\rho)$ for $\mathfrak b = (\beta)$. -/
theorem finsum_sphereCount_eq {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀))
    (hfree : GenusFree (formF Q₀) (stdLat F N)) (𝔟 : FracIdeal F) {β : F} (hβ : β ≠ 0)
    (hb : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton _ β) (ρ : F) :
    ∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F N),
        sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) ρ 𝔟 * ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹ =
      ENNReal.ofReal (repMass (formF Q₀) (stdLat F N) (β ^ 2 * ρ)) := by
  have hfin := genusClasses_finite hpd (stdLat F N) (HilbertModular.isIntegral_stdLat Q₀)
  unfold repMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    ENNReal.ofReal_sum_of_nonneg (fun c _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hcg := hfin.mem_toFinset.mp hc
  rw [sphereCount_eq_repCount Q₀ hpd hfree hcg 𝔟 hβ hb, div_eq_mul_inv,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, latClass_repCount_eq]

open QuadFormsKB.SphericalFibration QuadFormsKB.SphericalZeta FractionalIdeal in
/-- **Steps 1–5: the orbital series is an Euler product** (Weil 1982, §4.5, p. 109 [unverified]). For $\mathcal O_F$ a PID, $Q_0$ totally
positive definite in $n + 1 \ge 5$ variables, $\rho = \rho_k$, an adapted frame and the local orbital identity at every prime,
$$D_k(s) = \mathrm{Mass}(Q_0')\cdot\frac{\prod_\mathfrak p\alpha_\mathfrak p(Q_0')\prod_\mathfrak pD_\mathfrak p\prod_\mathfrak pZ_\mathfrak p(s,\rho)}{\prod_\mathfrak p\alpha_\mathfrak p(Q_0)}\qquad(s > 0),$$
$D_k$ = `orbitalSeries`, $D_\mathfrak p$ = `frameD`, $Z_\mathfrak p$ = `sphLocal`. -/
theorem orbitalSeries_toReal_eq [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (k : SqClasses F) (fr : AdaptedFrame (formF Q₀) (rep k))
    (hgli : ∀ v, OrbitalLocalIdentityAt v Q₀ fr) {s : ℝ} (hs : 0 < s) :
    (orbitalSeries Q₀ s k).toReal = mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F n) *
      ((∏' v, NF.siegelDensity v fr.Q' fr.Q') * (∏' v, frameD fr s v) *
        (∏' v, sphLocal Q₀ v (algebraMap F (v.adicCompletion F) (rep k)) s) / ∏' v, NF.siegelDensity v Q₀ Q₀) := by
  classical
  have hρ : rep k ≠ 0 := rep_ne_zero k
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  set QF' := fr.Q'.map (algebraMap (𝓞 F) F)
  set x : ℝ := ((n + 1 : ℕ) : ℝ) + 2 * s
  set f : HeightOneSpectrum (𝓞 F) → ℤ → ℝ := fun v j =>
    ((Ideal.absNorm v.asIdeal : ℝ) ^ j) ^ (-x) * locW v fr j
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q₀ Q₀
  set α' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v fr.Q' fr.Q'
  set Z : HeightOneSpectrum (𝓞 F) → ℝ := fun v => sphLocal Q₀ v (algebraMap F (v.adicCompletion F) (rep k)) s
  set D : HeightOneSpectrum (𝓞 F) → ℝ := frameD fr s
  have hqpos : ∀ v : HeightOneSpectrum (𝓞 F), (0 : ℝ) < Ideal.absNorm v.asIdeal := fun v => by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot))
  -- the local series
  have hloc : ∀ v, HasSum (f v) (α' v * D v * Z v / α v) := by
    intro v
    have h := hasSum_locW v Q₀ hQ₀ hρ fr (hgli v) hs.le
    convert h using 1
    simp only [α', D, Z, α, frameD]
    have hα := siegelDensity_pos v Q₀ hQ₀
    field_simp
  have hf0 : ∀ v j, 0 ≤ f v j := fun v j =>
    mul_nonneg (Real.rpow_nonneg (zpow_nonneg (hqpos v).le _) _) (locTypeSumG_nonneg v)
  -- the exceptional set
  have hfin₀ : {v : HeightOneSpectrum (𝓞 F) | frameLat v fr.g ≠ std v ∨ v.valuation F (rep k) ≠ 1 ∨
      v.valuation F 2 ≠ 1}.Finite := by
    refine ((Filter.eventually_cofinite.mp (loc_eventually_std (glImage_isLattice fr.g⁻¹ intVec_isLattice))).union
      ((finite_valuation_ne_one hρ).union (finite_valuation_ne_one (two_ne_zero (α := F))))).subset fun v hv => ?_
    simpa [frameLat, or_assoc] using hv
  set S₀ := hfin₀.toFinset
  have hW0 : ∀ v ∉ S₀, locW v fr 0 = 1 := by
    intro v hv
    simp only [S₀, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hv
    unfold locW
    rw [zpow_zero, hv.1]
    exact locTypeSumG_std_one_of_units v fr.Q' hQ'nd hv.2.1 hv.2.2
  have hf1 : ∀ v ∉ S₀, f v 0 = 1 := by
    intro v hv
    simp only [f, zpow_zero, Real.one_rpow, one_mul]
    exact hW0 v hv
  -- the Euler product
  have hαm : Multipliable α := multipliable_siegelDensity (N := n + 1) (by omega) (by omega) Q₀ hQ₀
  have hα'm : Multipliable α' := multipliable_siegelDensity (N := n) (by omega) (by omega) fr.Q' hQ'nd
  have hZm : Multipliable Z := multipliable_zf (Q := Q₀) hQ₀ (by omega) (Quotient.out k) hs.le
  have hDm : Multipliable D := by
    have hfinD := finite_frameD_ne_one fr hρ s
    refine multipliable_of_ne_finset_one (s := hfinD.toFinset) fun v hv => ?_
    by_contra h
    exact hv ((Set.Finite.mem_toFinset _).mpr h)
  have hαpos := tprod_siegelDensity_pos (N := n + 1) (by omega) Q₀ hQ₀
  have hP : HasProd (fun v => ∑' j, f v j) ((∏' v, α' v) * (∏' v, D v) * (∏' v, Z v) / ∏' v, α v) := by
    have e : (fun v => ∑' j, f v j) = fun v => α' v * D v * Z v / α v := funext fun v => (hloc v).tsum_eq
    rw [e]
    exact ((hα'm.hasProd.mul hDm.hasProd).mul hZm.hasProd).div₀ hαm.hasProd hαpos.ne'
  have hE := hasSum_finsupp_finprod f hf0 S₀ hf1 (fun v => (hloc v).summable) hP
  have hEb : HasSum (fun 𝔟 : FracIdeal F => ∏ᶠ v, f v (count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)))
      ((∏' v, α' v) * (∏' v, D v) * (∏' v, Z v) / ∏' v, α v) := by
    have := (fracIdealEquiv F).hasSum_iff.mpr hE
    convert this using 2 with 𝔟
    simp only [Function.comp_apply, fracIdealEquiv_apply]
  have hfree : GenusFree (formF Q₀) (stdLat F (n + 1)) := genusFree_of_isPrincipalIdealRing _ _
  have hpd' : IsTotallyPosDef QF' := by
    have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
    rw [fr.compMat_eq] at h1
    exact isTotallyPosDef_of_splitForm h1
  have hmass : 0 < mass QF' (stdLat F n) := mass_pos hpd' (stdLat F n) (HilbertModular.isIntegral_stdLat fr.Q')
  have hterm : ∀ 𝔟 : FracIdeal F,
      ENNReal.ofReal (idealNorm F 𝔟 ^ (-(((n + 1 : ℕ) : ℝ) + 2 * s))) *
        ∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F (n + 1)),
          sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) (rep k) 𝔟 *
            ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹ =
      ENNReal.ofReal (mass QF' (stdLat F n) * ∏ᶠ v, f v (count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) := by
    intro 𝔟
    set I : FractionalIdeal (𝓞 F)⁰ F := (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
    have hprin := FractionalIdeal.eq_spanSingleton_of_principal I
    set β := Submodule.IsPrincipal.generator (I : Submodule (𝓞 F) F)
    have hβ : β ≠ 0 := by
      intro h0; apply 𝔟.ne_zero
      show I = 0
      rw [hprin, h0, FractionalIdeal.spanSingleton_zero]
    rw [finsum_sphereCount_eq Q₀ hpd hfree 𝔟 hβ hprin, repMass_eq_mass_mul_finprod Q₀ hpd hρ fr hβ]
    have hT : ∀ v, locTypeSumG v (rep k) QF' (frameLat v fr.g) (algebraMap F (v.adicCompletion F) β) =
        locW v fr (count F v I) := by
      intro v; rw [locTypeSumG_frame_eq_locW v fr hQ'nd hβ, ← hprin]
    rw [finprod_congr hT]
    -- everything is a product over a finite set `T`
    have hcfin : {v : HeightOneSpectrum (𝓞 F) | count F v I ≠ 0}.Finite :=
      Filter.eventually_cofinite.mp (finite_factors I)
    set T := hcfin.toFinset ∪ S₀
    have hcT : ∀ v ∉ T, count F v I = 0 := by
      intro v hv; by_contra h; exact hv (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
    have hS₀T : ∀ v ∉ T, v ∉ S₀ := fun v hv h => hv (Finset.mem_union_right _ h)
    have e1 : idealNorm F 𝔟 = ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^ count F v I := by
      rw [idealNorm_eq_finprod]
      refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
      by_contra h; apply hv
      show (Ideal.absNorm v.asIdeal : ℝ) ^ count F v I = 1
      rw [hcT v h, zpow_zero]
    have e2 : ∏ᶠ v, locW v fr (count F v I) = ∏ v ∈ T, locW v fr (count F v I) := by
      refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
      by_contra h; apply hv
      show locW v fr (count F v I) = 1
      rw [hcT v h]; exact hW0 v (hS₀T v h)
    have e3 : ∏ᶠ v, f v (count F v I) = ∏ v ∈ T, f v (count F v I) := by
      refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
      by_contra h; apply hv
      show f v (count F v I) = 1
      rw [hcT v h]; exact hf1 v (hS₀T v h)
    rw [e1, e2, e3, ← Real.finsetProd_rpow _ _ (fun v _ => zpow_nonneg (hqpos v).le _),
      ← ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (zpow_nonneg (hqpos v).le _) _)]
    congr 1
    simp only [f, Finset.prod_mul_distrib]
    ring
  show (∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-(((n + 1 : ℕ) : ℝ) + 2 * s))) *
        ∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F (n + 1)),
          sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) (rep k) 𝔟 *
            ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹).toReal = _
  simp_rw [hterm]
  have hnn : ∀ 𝔟 : FracIdeal F, 0 ≤ mass QF' (stdLat F n) * ∏ᶠ v, f v (count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :=
    fun 𝔟 => mul_nonneg hmass.le (finprod_nonneg fun v => hf0 v _)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hEb.summable.mul_left _), ENNReal.toReal_ofReal (tsum_nonneg hnn),
    tsum_mul_left, hEb.tsum_eq]

end Euler

/-! ### The product formula and the archimedean constants -/

section Arch

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

open NumberField.InfinitePlace in
/-- **Embeddings are real places** for $F$ totally real: $\sigma \mapsto$ the place of $\sigma$. -/
def embPlace : (F →ₐ[ℚ] ℂ) ≃ Siegel.RealPlace F :=
  (RingHom.equivRatAlgHom F ℂ).symm.trans
    ((Equiv.subtypeUnivEquiv fun φ => IsTotallyReal.complexEmbedding_isReal φ).symm.trans mkReal)

theorem abs_realEmb_embPlace (σ : F →ₐ[ℚ] ℂ) (x : F) : |realEmb F (embPlace σ).1 x| = ‖σ x‖ := by
  rw [← SphericalFibration.realEmb_siegel, Siegel.abs_realEmb]
  rfl

/-- **The product formula** for $x \in F^\times$: $\prod_\mathfrak p|x|_\mathfrak p = \big(\prod_\sigma|\sigma x|\big)^{-1}$. -/
theorem finprod_norm_eq (x : F) (hx : x ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) x‖ =
      (∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖)⁻¹ := by
  have h := WeilRep.prod_modulus_eq_one (F := F) hx
  have hm : ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) x) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) x‖ :=
    finprod_congr fun v => WeilRep.modK_eq_norm v ((map_ne_zero _).mpr hx)
  rw [hm, mixedEmbedding.norm_eq_norm] at h
  rw [prod_norm_embeddings]
  push_cast at h
  exact eq_inv_of_mul_eq_one_right h

theorem finprod_eq_prod_of_one {ι : Type*} {f : ι → ℝ} (T : Finset ι) (hT : ∀ v ∉ T, f v = 1) :
    ∏ᶠ v, f v = ∏ v ∈ T, f v :=
  finprod_eq_prod_of_mulSupport_subset _ fun v hv => by by_contra h; exact hv (hT v h)

theorem norm_algebraMap_eq_one' {x : F} {v : HeightOneSpectrum (𝓞 F)} (hx : v.valuation F x = 1) :
    ‖algebraMap F (v.adicCompletion F) x‖ = 1 := norm_algebraMap_eq_one hx

/-- **The product formula for the frame factors**: $\prod_\mathfrak pD_\mathfrak p = \prod_\sigma|\sigma\det g|^{-(n+1)}|\sigma(2\rho)|^n|\sigma\rho|^{1+s}|\sigma2|$. -/
theorem finprod_frameD {Q : QuadForm F (n + 1)} {ρ : F} (fr : AdaptedFrame Q ρ) (hρ : ρ ≠ 0) (s : ℝ) :
    ∏ᶠ v, frameD fr s v = ∏ σ : F →ₐ[ℚ] ℂ, (‖σ fr.g.val.det‖ ^ (n + 1))⁻¹ * ‖σ (2 * ρ)‖ ^ n *
      ‖σ ρ‖ ^ (1 + s) * ‖σ 2‖ := by
  classical
  have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
  have h2ρ : (2 * ρ : F) ≠ 0 := mul_ne_zero two_ne_zero hρ
  have hfin := ((finite_valuation_ne_one hdet).union ((finite_valuation_ne_one hρ).union
    ((finite_valuation_ne_one (two_ne_zero (α := F))).union (finite_valuation_ne_one h2ρ))))
  set T := hfin.toFinset
  have hT : ∀ v ∉ T, v.valuation F fr.g.val.det = 1 ∧ v.valuation F ρ = 1 ∧ v.valuation F 2 = 1 ∧
      v.valuation F (2 * ρ) = 1 := by
    intro v hv
    simp only [T, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
    exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩
  set A : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖
  set B : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖
  set C : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖algebraMap F (v.adicCompletion F) ρ‖
  set E : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖algebraMap F (v.adicCompletion F) 2‖
  have hpos : ∀ (x : F), x ≠ 0 → ∀ v : HeightOneSpectrum (𝓞 F), 0 < ‖algebraMap F (v.adicCompletion F) x‖ :=
    fun x hx v => norm_pos_iff.mpr ((map_ne_zero _).mpr hx)
  have hD : ∀ v, frameD fr s v = A v ^ (n + 1) / B v ^ n * (C v ^ (-(1 + s)) * (E v)⁻¹) := by
    intro v
    simp only [frameD, A, B, C, E, map_mul, map_ofNat]
  have hA : ∏ᶠ v, A v = ∏ v ∈ T, A v := finprod_eq_prod_of_one T fun v hv => norm_algebraMap_eq_one (hT v hv).1
  have hB : ∏ᶠ v, B v = ∏ v ∈ T, B v := finprod_eq_prod_of_one T fun v hv => norm_algebraMap_eq_one (hT v hv).2.2.2
  have hC : ∏ᶠ v, C v = ∏ v ∈ T, C v := finprod_eq_prod_of_one T fun v hv => norm_algebraMap_eq_one (hT v hv).2.1
  have hE : ∏ᶠ v, E v = ∏ v ∈ T, E v := finprod_eq_prod_of_one T fun v hv => norm_algebraMap_eq_one (hT v hv).2.2.1
  have hDT : ∏ᶠ v, frameD fr s v = ∏ v ∈ T, frameD fr s v :=
    finprod_eq_prod_of_one T fun v hv => frameD_eq_one fr s (hT v hv).1 (hT v hv).2.1 (hT v hv).2.2.1
  rw [hDT, Finset.prod_congr rfl fun v _ => hD v, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_pow, Finset.prod_inv_distrib,
    Real.finsetProd_rpow _ _ (fun v _ => (norm_nonneg _)), ← hA, ← hB, ← hC, ← hE]
  simp only [A, B, C, E]
  rw [finprod_norm_eq _ hdet, finprod_norm_eq _ h2ρ, finprod_norm_eq _ hρ, finprod_norm_eq _ two_ne_zero]
  have hp : ∀ x : F, x ≠ 0 → 0 < ∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖ := fun x hx =>
    Finset.prod_pos fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hx)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_pow, Finset.prod_pow, Real.finsetProd_rpow _ _ (fun σ _ => norm_nonneg _),
    Real.inv_rpow (hp ρ hρ).le, Real.rpow_neg (hp ρ hρ).le, inv_inv, inv_inv]
  have h1 := (hp _ hdet).ne'
  have h2 := (hp _ h2ρ).ne'
  rw [inv_pow, inv_pow, div_inv_eq_mul]
  field_simp

/-- Scaling of the archimedean volume: $\mathrm{vol}(SO_n, d/c^2) = c^{n+1}\,\mathrm{vol}(SO_n, d)$. -/
theorem archVolSO_div_sq (m : ℕ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    archVolSO m (d / c ^ 2) = archVolSO m d * c ^ (m + 1) := by
  unfold archVolSO
  rw [Real.div_rpow hd.le (by positivity), ← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le,
    show ((2 : ℕ) : ℝ) * (-((m : ℝ) + 1) / 2) = -(((m + 1 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_neg hc.le,
    Real.rpow_natCast]
  have : c ^ (m + 1) ≠ 0 := by positivity
  field_simp

/-- **The archimedean identity at one real place** (Weil's fibration $SO_{n+1}(\mathbb R) \to S^n$ in Gram coordinates): with
$a = \sigma\rho > 0$, $c = |\sigma\det g|$, $D' = \det A'_\sigma$ and $D_0 = aD'/c^2 = \det A_\sigma$,
$\mathrm{vol}(SO_{n+1}, D_0)\,c^{-(n+1)}(2a)^na^{1+s}\cdot2 = \mathrm{vol}(SO_n, D')\cdot\frac{2\pi^{(n+1)/2}a^{(n+1)/2+s}}{\Gamma(\frac{n+1}2)\sqrt{D_0}}$. -/
theorem arch_alg (m : ℕ) {a c D' : ℝ} (ha : 0 < a) (hc : 0 < c) (hD : 0 < D') (s : ℝ) :
    archVolSO (m + 1) (a * D' / c ^ 2) * ((c ^ (m + 1))⁻¹ * (2 * a) ^ m * a ^ (1 + s) * 2) =
      archVolSO m D' * (2 * Real.pi ^ (((m + 1 : ℕ) : ℝ) / 2) * a ^ (((m + 1 : ℕ) : ℝ) / 2 + s) /
        Real.Gamma (((m + 1 : ℕ) : ℝ) / 2) * (Real.sqrt (a * D' / c ^ 2))⁻¹) := by
  have hX : 0 < D' / c ^ 2 := by positivity
  have h1 := archVolSO_succ m ha hX
  rw [show a * (D' / c ^ 2) = a * D' / c ^ 2 by ring] at h1
  rw [archVolSO_div_sq m hD hc] at h1
  unfold archRepDensity at h1
  have hsq : (Real.sqrt (a * D' / c ^ 2))⁻¹ = (a * D' / c ^ 2) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity)]
  rw [hsq]
  have hapow : a ^ (((m + 1 : ℕ) : ℝ) / 2 + s) = a ^ ((((m + 1 : ℕ) : ℝ) - 2) / 2) * a ^ (1 + s) := by
    rw [← Real.rpow_add ha]; congr 1; ring
  rw [hapow]
  calc archVolSO (m + 1) (a * D' / c ^ 2) * ((c ^ (m + 1))⁻¹ * (2 * a) ^ m * a ^ (1 + s) * 2)
      = (archVolSO (m + 1) (a * D' / c ^ 2) * (2 * a) ^ m) * (c ^ (m + 1))⁻¹ * a ^ (1 + s) * 2 := by ring
    _ = archVolSO m D' * c ^ (m + 1) * (Real.pi ^ (((m + 1 : ℕ) : ℝ) / 2) / Real.Gamma (((m + 1 : ℕ) : ℝ) / 2) *
          a ^ ((((m + 1 : ℕ) : ℝ) - 2) / 2) * (a * D' / c ^ 2) ^ (-(1 / 2 : ℝ))) * (c ^ (m + 1))⁻¹ *
          a ^ (1 + s) * 2 := by rw [h1]
    _ = _ := by
      have hc' : c ^ (m + 1) ≠ 0 := by positivity
      field_simp

/-- The determinant relation of a frame: $\det A_0\,(\det g)^2 = \rho\det A'$ ($A = H/2$), at every embedding. -/
theorem detGram_frame (Q₀ : QuadForm (𝓞 F) (n + 1)) {ρ : F} (fr : AdaptedFrame (formF Q₀) ρ) (σ : F →ₐ[ℚ] ℂ) :
    detGram Q₀ σ * ‖σ fr.g.val.det‖ ^ 2 = ‖σ ρ‖ * detGram fr.Q' σ := by
  have h1 := congrArg (fun S : QuadForm F (n + 1) => S.hessian.det) fr.compMat_eq
  simp only [hessian_compMat, det_mul, det_transpose, det_hessian_splitForm, hessian_map,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  have h2 : algebraMap (𝓞 F) F Q₀.hessian.det / 2 ^ (n + 1) * fr.g.val.det ^ 2 =
      ρ * (algebraMap (𝓞 F) F fr.Q'.hessian.det / 2 ^ n) := by
    rw [pow_succ]
    field_simp
    linear_combination h1
  unfold detGram
  rw [← norm_pow, ← norm_mul, ← map_pow, ← map_mul, h2, map_mul, norm_mul]

/-- **The archimedean identity of the frame at one embedding** (`arch_alg` with $a = \sigma\rho$, $c = |\sigma\det g|$, $D' = \det A'_\sigma$). -/
theorem arch_place (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {ρ : F}
    (fr : AdaptedFrame (formF Q₀) ρ) (hpos : ∀ v : InfinitePlace F, 0 < realEmb F v ρ) (s : ℝ)
    (σ : F →ₐ[ℚ] ℂ) :
    archVolSO (n + 1) (detGram Q₀ σ) *
        ((‖σ fr.g.val.det‖ ^ (n + 1))⁻¹ * ‖σ (2 * ρ)‖ ^ n * ‖σ ρ‖ ^ (1 + s) * ‖σ 2‖) =
      archVolSO n (detGram fr.Q' σ) * SphericalFibration.orbitalArch Q₀ s ρ (embPlace σ) := by
  have hρ : ρ ≠ 0 := by
    intro h; have := hpos (embPlace σ).1; rw [h, map_zero] at this; exact lt_irrefl 0 this
  have hQF := hpd.nondegenerate
  have hQ'nd := fr.nondegenerate hQF hρ
  set a := ‖σ ρ‖
  set c := ‖σ fr.g.val.det‖
  set D' := detGram fr.Q' σ
  have ha : 0 < a := norm_pos_iff.mpr ((map_ne_zero σ).mpr hρ)
  have hc : 0 < c := norm_pos_iff.mpr ((map_ne_zero σ).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero)
  have hD' : 0 < D' := by
    refine norm_pos_iff.mpr ((map_ne_zero σ).mpr (div_ne_zero ?_ (pow_ne_zero _ two_ne_zero)))
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ'nd
  have hD₀ : detGram Q₀ σ = a * D' / c ^ 2 := by
    rw [eq_div_iff (by positivity)]; exact detGram_frame Q₀ fr σ
  have h2 : ‖σ (2 : F)‖ = 2 := by rw [map_ofNat, Complex.norm_ofNat]
  have h2ρ : ‖σ (2 * ρ)‖ = 2 * a := by rw [map_mul, norm_mul, h2]
  rw [hD₀, h2ρ, h2]
  -- the archimedean constant of the orbital Euler product
  have hrρ : realEmb F (embPlace σ).1 ρ = a := by
    have := abs_realEmb_embPlace σ ρ
    rwa [abs_of_pos (hpos _)] at this
  have hdetw : ((gramF Q₀).map (realEmb F (embPlace σ).1)).det = a * D' / c ^ 2 := by
    rw [← hD₀]
    have hpd' := (isTotPosGram_of_isTotallyPosDef hpd) (embPlace σ).1
    have hpos' := hpd'.det_pos
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hpos' ⊢
    have hg : (gramF Q₀).det = algebraMap (𝓞 F) F Q₀.hessian.det / 2 ^ (n + 1) := by
      rw [gramF, Matrix.det_smul, Fintype.card_fin, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      field_simp
      have h2n : (2 : F) ^ (n + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
      rw [div_pow, one_pow, mul_comm (1 / 2 ^ (n + 1)), mul_assoc, one_div, inv_mul_cancel₀ h2n, mul_one]
    unfold detGram
    rw [← abs_realEmb_embPlace σ, ← hg, abs_of_pos hpos']
  unfold SphericalFibration.orbitalArch
  rw [hrρ, hdetw]
  exact arch_alg n ha hc hD' s

end Arch

/-! ### Step 5 completed: the orbital Euler product identity with all constants -/

section Constants

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

open QuadFormsKB.SphericalFibration QuadFormsKB.SphericalZeta Classical in
/-- **The orbital Euler product for one square class** (Weil 1982, §4.5, p. 109; $\mathcal O_F$ a PID): for $Q_0$ totally positive definite
in $N = n + 1 \ge 5$ variables, $\rho = \rho_k$ totally positive, an adapted frame $Q_0\circ g = \langle\rho\rangle\perp Q_0'$ and the local orbital
identity of the frame at every prime,
$$2\mu\,D_k(s) = \tau(SO(Q_0'))\,|d_F|^{-\frac{N-1}2}\prod_w\frac{2\pi^{N/2}\sigma_w(\rho)^{\frac N2+s}}{\Gamma(\frac N2)\sqrt{\det A_w}}\prod_\mathfrak pZ_\mathfrak p(s,\rho).$$
The constant is the stabilizer's $\tau(SO(Q_0')) = 2\mu(Q_0')\mathrm{Mass}(Q_0')$ (`tauSO`); no induction hypothesis is used here. -/
@[kb "weil1982" "§4.5, p. 109 (Z⁺(s) unfolded over T(ρ), the orbital Euler product) [unverified]"]
theorem two_mul_tamagawaK_orbitalSeries [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (k : SqClasses F) (fr : AdaptedFrame (formF Q₀) (rep k))
    (hgli : ∀ v, OrbitalLocalIdentityAt v Q₀ fr) {s : ℝ} (hs : 0 < s)
    (hpos : ∀ v : InfinitePlace F, 0 < realEmb F v (rep k)) :
    2 * tamagawaK Q₀ * (orbitalSeries Q₀ s k).toReal =
      tauSO fr.Q' * |(NumberField.discr F : ℝ)| ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) *
        (∏ w, orbitalArch Q₀ s (rep k) w) *
        ∏' v : HeightOneSpectrum (𝓞 F), sphLocal Q₀ v (algebraMap F (v.adicCompletion F) (rep k)) s := by
  have hρ : rep k ≠ 0 := rep_ne_zero k
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  have hpd' : IsTotallyPosDef (fr.Q'.map (algebraMap (𝓞 F) F)) := by
    have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
    rw [fr.compMat_eq] at h1
    exact isTotallyPosDef_of_splitForm h1
  rw [orbitalSeries_toReal_eq Q₀ hpd hn k fr hgli hs]
  have htau : tauSO fr.Q' = tamagawaK fr.Q' * (2 * mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F n)) := by
    rw [tauSO, mass_SO_eq_two_mul_mass fr.Q' hQ'nd (by omega) hpd' (HilbertModular.isIntegral_stdLat fr.Q')]
  rw [htau]
  -- the frame factors through the product formula
  have hDfin : Function.HasFiniteMulSupport (frameD fr s) := by
    have := finite_frameD_ne_one fr hρ s
    exact this.subset fun v hv => hv
  rw [tprod_eq_finprod hDfin, finprod_frameD fr hρ s]
  set A := ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ Q₀
  set A' := ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v fr.Q' fr.Q'
  set Z := ∏' v : HeightOneSpectrum (𝓞 F), sphLocal Q₀ v (algebraMap F (v.adicCompletion F) (rep k)) s
  set M := mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F n)
  set δ := |(NumberField.discr F : ℝ)|
  have hδ : 0 < δ := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have hA : A ≠ 0 := (tprod_siegelDensity_pos (N := n + 1) (by omega) Q₀ hQ₀).ne'
  -- the archimedean products
  have key : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram Q₀ σ)) *
      (∏ σ : F →ₐ[ℚ] ℂ, (‖σ fr.g.val.det‖ ^ (n + 1))⁻¹ * ‖σ (2 * rep k)‖ ^ n * ‖σ (rep k)‖ ^ (1 + s) * ‖σ 2‖) =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram fr.Q' σ)) * ∏ w, orbitalArch Q₀ s (rep k) w := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun σ _ => arch_place Q₀ hpd fr hpos s σ,
      Finset.prod_mul_distrib]
    congr 1
    exact Fintype.prod_equiv embPlace _ _ fun σ => rfl
  have hδe : δ ^ (-((((n + 1 : ℕ) : ℝ)) * (((n + 1 : ℕ) : ℝ) - 1) / 4)) =
      δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add hδ]; push_cast; ring_nf
  unfold tamagawaK
  rw [hδe]
  calc 2 * (δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) *
        (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram Q₀ σ)) * A) *
        (M * (A' * (∏ σ : F →ₐ[ℚ] ℂ, (‖σ fr.g.val.det‖ ^ (n + 1))⁻¹ * ‖σ (2 * rep k)‖ ^ n *
          ‖σ (rep k)‖ ^ (1 + s) * ‖σ 2‖) * Z / A))
      = 2 * (δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2)) * M * A' * Z *
          ((∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram Q₀ σ)) *
            (∏ σ : F →ₐ[ℚ] ℂ, (‖σ fr.g.val.det‖ ^ (n + 1))⁻¹ * ‖σ (2 * rep k)‖ ^ n *
              ‖σ (rep k)‖ ^ (1 + s) * ‖σ 2‖)) := by
        field_simp
    _ = _ := by rw [key]; ring

end Constants

/-! ### Square classes not represented by $Q$: both sides vanish -/

section NotRep

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

theorem evalIn_formF {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (K : Type*) [Field K] [Algebra F K] [Algebra (𝓞 F) K]
    [IsScalarTower (𝓞 F) F K] (x : Fin N → K) : (formF Q₀).evalIn K x = Q₀.evalIn K x := by
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, ← IsScalarTower.algebraMap_apply]

open QuadFormsKB.SphericalFibration QuadFormsKB.SphericalZeta in
/-- If $Q$ does not represent $\rho_k$ over $F$, the orbital series vanishes (no class has a vector of norm $\rho_k$ in any $\mathfrak b^{-1}M$). -/
theorem orbitalSeries_eq_zero_of_not_rep {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hfree : GenusFree (formF Q₀) (stdLat F N))
    (k : SqClasses F) (h : ¬ ∃ ξ : Fin N → F, (formF Q₀).eval ξ = rep k) (s : ℝ) : orbitalSeries Q₀ s k = 0 := by
  classical
  unfold orbitalSeries
  refine ENNReal.tsum_eq_zero.mpr fun 𝔟 => ?_
  have hz : ∀ c ∈ genusClasses (formF Q₀) (stdLat F N),
      sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) (rep k) 𝔟 *
        ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹ = 0 := by
    intro c hc
    obtain ⟨γ, hi, -, hcf⟩ := classForm_spec' Q₀ hfree hc
    have : sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) (rep k) 𝔟 = 0 := by
      unfold sphereCount
      refine ENNReal.tsum_eq_zero.mpr fun η => ?_
      rw [if_neg]
      rintro ⟨hη, -⟩
      rw [hcf, qv_gramF, gramZ_map, eval_gramFormF_col] at hη
      exact h ⟨_, hη⟩
    rw [this, zero_mul]
  rw [show (∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F N), sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) (rep k) 𝔟 *
      ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹) = 0 from
    (finsum_mem_congr rfl hz).trans (finsum_mem_zero _), mul_zero]

/-- A totally positive definite form represents every totally positive $\rho$ over a real completion. -/
theorem representsIn_real (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {ρ : F}
    (hpos : ∀ v : InfinitePlace F, 0 < realEmb F v ρ) (w : InfinitePlace F) :
    (formF Q₀).RepresentsIn w.Completion ρ := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have he : ∀ c : F, e (algebraMap F w.Completion c) = realEmb F w c := fun c => by
    rw [QuadFormsKB.HN.real_algebraMap hw c]; rfl
  set x₀ : Fin (n + 1) → F := Pi.single 0 1
  have hx₀ : x₀ ≠ 0 := by
    intro h; have := congrFun h 0; simp [x₀] at this
  set c := (formF Q₀).eval x₀
  have hc : 0 < realEmb F w c := by
    have := realEmb_qv_pos (isTotPosGram_of_isTotallyPosDef hpd) w hx₀
    rwa [qv_gramF] at this
  set t : w.Completion := e.symm (Real.sqrt (realEmb F w ρ / realEmb F w c))
  refine ⟨t • fun i => algebraMap F w.Completion (x₀ i), ?_⟩
  apply e.injective
  have hev : (formF Q₀).evalIn w.Completion (fun i => algebraMap F w.Completion (x₀ i)) =
      algebraMap F w.Completion c := by
    simp only [c, QuadForm.evalIn, map_sum, apply_ite, map_mul, map_zero,
      Algebra.algebraMap_self, RingHom.id_apply]
  rw [evalIn_smul', hev, map_mul, map_pow, he, he]
  simp only [t, RingEquiv.apply_symm_apply]
  rw [Real.sq_sqrt (div_nonneg (hpos w).le hc.le), div_mul_cancel₀ _ hc.ne']

open QuadFormsKB.SphericalZeta in
/-- If $Q$ does not represent $\rho$ over $F$ ($\rho$ totally positive), some local factor $Z_\mathfrak p(s,\rho)$ vanishes (Hasse–Minkowski:
$Q$ fails to represent $\rho$ over some $F_\mathfrak p$, the real places being represented), so $\prod_\mathfrak pZ_\mathfrak p = 0$. -/
theorem tprod_sphLocal_eq_zero (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {ρ : F}
    (hρ : ρ ≠ 0) (hpos : ∀ v : InfinitePlace F, 0 < realEmb F v ρ) (h : ¬ ∃ ξ, (formF Q₀).eval ξ = ρ) (s : ℝ) :
    ∏' v : HeightOneSpectrum (𝓞 F), sphLocal Q₀ v (algebraMap F (v.adicCompletion F) ρ) s = 0 := by
  have hQF := hpd.nondegenerate
  have hnot : ¬ (formF Q₀).RepresentsIn F ρ := by
    rintro ⟨x, hx⟩; exact h ⟨x, hx⟩
  rw [represents_iff_everywhere_nf (formF Q₀) hQF ρ hρ] at hnot
  simp only [NFPlace.Everywhere, not_forall] at hnot
  obtain ⟨p, hp⟩ := hnot
  cases p with
  | infinite w => exact absurd (representsIn_real Q₀ hpd hpos w) hp
  | finite v =>
    refine tprod_of_exists_eq_zero ⟨v, ?_⟩
    have hempty : LocalZeta.latL v (n + 1) ∩ (NF.Qp v Q₀).evalIn (v.adicCompletion F) ⁻¹'
        sqClass (algebraMap F (v.adicCompletion F) ρ) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false, not_and]
      rintro - ⟨y, hy, hxy⟩
      apply hp
      refine ⟨y⁻¹ • x, ?_⟩
      rw [evalIn_smul', evalIn_formF, ← NF.evalIn_Qp v, hxy]
      field_simp
    unfold sphLocal sphInt
    rw [hempty, MeasureTheory.Measure.restrict_empty, MeasureTheory.integral_zero_measure, mul_zero, zero_div]

end NotRep

/-! ### The orbital Euler product, and $\tau(SO(V)) = 2$ from the induction hypothesis -/

section Main

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

open QuadFormsKB.SphericalZeta

/-- **Input: the local orbital identities at the non-standard primes** (Weil 1982, §3.4 [unverified]; Kitaoka 1993, §5.6
[unverified]): for every $\rho \in F^\times$, every frame $Q_0\circ g = \langle\rho\rangle\perp Q_0'$ and every prime $\mathfrak p$ that is **not** a standard
prime of the frame, `OrbitalLocalIdentityAt`.

Field:
- `nonstd`: the local identity at the non-standard primes.

*Status and hygiene.* A family of purely local statements, one prime at a time (finitely many primes for each frame); it does not
mention classes, masses or $\tau$, and it is not equivalent to $\tau(SO(V)) = 2$. At the standard primes (all but finitely many,
dyadic ones included when the frame is standard there) the identity is **proved** (`orbitalLocalIdentityAt_std`). What remains are
the primes where $g^{-1}\mathcal O_F^{n+1}$ is not $\mathfrak o_\mathfrak p^{n+1}$ (the vector $\xi = ge_0$ of norm $\rho$ is not a split vector of $L_\mathfrak p$, e.g.
$\mathfrak p \mid \rho$ with $\mathrm{ord}_\mathfrak p\rho$ odd and $L_\mathfrak p$ unimodular) or $\mathrm{ord}_\mathfrak p\rho \ge 2$. -/
@[kb "weil1982" "§3.4 (local fibration at the non-standard primes of a frame) [unverified]"]
structure OrbitalLocalIdentities (Q₀ : QuadForm (𝓞 F) (n + 1)) : Prop where
  nonstd : ∀ (ρ : F) (fr : AdaptedFrame (formF Q₀) ρ) (v : HeightOneSpectrum (𝓞 F)), ρ ≠ 0 →
    ¬ IsStdPrime v fr → OrbitalLocalIdentityAt v Q₀ fr

theorem orbitalLocalIdentityAt_all {Q₀ : QuadForm (𝓞 F) (n + 1)} (hloc : OrbitalLocalIdentities Q₀)
    (hQ₀ : Q₀.Nondegenerate) (hn : 1 ≤ n) {ρ : F} (hρ : ρ ≠ 0) (fr : AdaptedFrame (formF Q₀) ρ)
    (v : HeightOneSpectrum (𝓞 F)) : OrbitalLocalIdentityAt v Q₀ fr := by
  by_cases hs : IsStdPrime v fr
  · exact orbitalLocalIdentityAt_std v Q₀ hQ₀ hn hρ fr hs
  · exact hloc.nonstd ρ fr v hρ hs

/-- The chosen adapted frame of a square class represented by $Q$. -/
def chosenFrame (Q₀ : QuadForm (𝓞 F) (n + 1)) (k : SqClasses F) (h : ∃ ξ, (formF Q₀).eval ξ = rep k) :
    AdaptedFrame (formF Q₀) (rep k) :=
  Classical.choice (exists_adaptedFrame (formF Q₀) h.choose_spec (rep_ne_zero k))

open Classical in
/-- **The stabilizers' Tamagawa numbers** $\tau'_k = \tau(SO(Q_0'))$ for the complement $Q_0'$ of a vector of norm $\rho_k$ (chosen frame),
and $2$ for the square classes not represented by $Q$ (where both sides of the orbital Euler product vanish). -/
def tauComp (Q₀ : QuadForm (𝓞 F) (n + 1)) (k : SqClasses F) : ℝ :=
  if h : ∃ ξ, (formF Q₀).eval ξ = rep k then tauSO (chosenFrame Q₀ k h).Q' else 2

open QuadFormsKB.SphericalFibration QuadFormsKB.SphericalZeta Classical in
/-- **The orbital Euler product holds** (`OrbitalEulerProduct`, Weil 1982, §4.5, p. 109), for $\mathcal O_F$ a PID, $Q_0$ totally positive
definite in $n + 1 \ge 5$ variables, with $\tau'_k = \tau(SO(Q_{0,k}'))$ the Tamagawa numbers of the complements (`tauComp`), given the local
orbital identities at the finitely many non-standard primes of each frame (`OrbitalLocalIdentities`). -/
@[kb "weil1982" "§4.5, p. 109 (the orbital Euler product: Siegel's theorem for the numbers ρb² with τ(G'), summed over 𝔟)"]
theorem orbitalEulerProduct [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (hloc : OrbitalLocalIdentities Q₀) :
    OrbitalEulerProduct Q₀ (tauComp Q₀) := by
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  refine ⟨fun k s hs hpos => ?_⟩
  by_cases h : ∃ ξ, (formF Q₀).eval ξ = rep k
  · rw [tauComp, dif_pos h]
    exact two_mul_tamagawaK_orbitalSeries Q₀ hpd hn k (chosenFrame Q₀ k h)
      (fun v => orbitalLocalIdentityAt_all hloc hQ₀ (by omega) (rep_ne_zero k) _ v) hs hpos
  · rw [orbitalSeries_eq_zero_of_not_rep Q₀ (genusFree_of_isPrincipalIdealRing _ _) k h s,
      tprod_sphLocal_eq_zero Q₀ hpd (rep_ne_zero k) hpos h s]
    simp

/-- **The induction hypothesis gives `ComplementTauTwo`**: if $\tau(SO(Q')) = 2$ for every totally positive definite $Q'$ in $n$ variables
over $\mathcal O_F$, then $\tau'_k = 2$ for every square class. -/
theorem complementTauTwo_of_IH (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    (hIH : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q') :
    ComplementTauTwo (tauComp Q₀) := by
  refine ⟨fun k => ?_⟩
  unfold tauComp
  split_ifs with h
  · set fr := chosenFrame Q₀ k h
    have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
    rw [fr.compMat_eq] at h1
    exact hIH fr.Q' (isTotallyPosDef_of_splitForm h1)
  · rfl

/-- **Weil's Theorem 4.5.1, $\tau(SO(V)) = 2$, from the induction hypothesis** (Weil 1982, §4.5, Thm 4.5.1, p. 109):
for $F$ totally real with $\mathcal O_F$ a PID and $Q_0$ totally positive definite in $n + 1 \ge 5$ variables over
$\mathcal O_F$, if $\tau(SO) = 2$ in rank $n$ (`hIH`, the induction hypothesis: every totally positive definite form
in $n$ variables) and the local orbital identities hold at the non-standard primes of the frames
(`OrbitalLocalIdentities`, a per-prime local input), then $\tau(SO(V)) = 2$. -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109 (induction step n → n+1)"]
theorem tamagawaNumberTwo_of_complement [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (hloc : OrbitalLocalIdentities Q₀)
    (hIH : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q') :
    TamagawaNumberTwo Q₀ := by
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  exact SphericalFibration.tamagawaNumberTwo_of_orbitalEulerProduct' Q₀ hQ₀ (by omega) hpd
    (orbitalEulerProduct Q₀ hpd hn hloc) (complementTauTwo_of_IH Q₀ hpd hIH)

/-- **The mass formula in rank $n + 1 \ge 5$ from the induction hypothesis** (`massFormula` with $\tau = 2$):
$\mathrm{Mass}(\mathcal O_F^{n+1}) = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$. -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; cf. Kitaoka 1993, Thm 6.8.1 [unverified]"]
theorem massFormula_of_complement [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (hloc : OrbitalLocalIdentities Q₀)
    (hIH : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q') :
    mass (formF Q₀) (stdLat F (n + 1)) = (tamagawaK Q₀)⁻¹ := by
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  exact massFormula Q₀ hQ₀ (by omega) hpd (HilbertModular.isIntegral_stdLat Q₀)
    (tamagawaNumberTwo_of_complement Q₀ hpd hn hloc hIH)

/-- **Siegel's formula for the number $m$ in rank $n + 1 \ge 5$** for split forms $\langle m\rangle\perp Q_0'$
(`siegelFormulaAt_of_tamagawa'` with $\tau = 2$ in rank $n + 1$; $\tau(SO(Q_0')) = 2$ is part of the induction
hypothesis). -/
@[kb "weil1982" "§4.5, p. 100 (Siegel's theorem as a consequence of τ = 2), Thm 4.5.1, p. 109"]
theorem siegelFormulaAt_of_complement [IsPrincipalIdealRing (𝓞 F)] (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hn : 4 ≤ n) (hpd : IsTotallyPosDef (formF (splitForm m₀ Q₀')))
    (hloc : OrbitalLocalIdentities (splitForm m₀ Q₀'))
    (hIH : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q') :
    SiegelFormulaAt (splitForm m₀ Q₀') m₀ := by
  have hpd' : IsTotallyPosDef (formF Q₀') := by
    have := isTotallyPosDef_of_splitForm (m := algebraMap (𝓞 F) F m₀) (Q' := Q₀'.map (algebraMap (𝓞 F) F))
      (by rw [← map_splitForm]; exact hpd)
    exact this
  exact siegelFormulaAt_of_tamagawa' m₀ hm Q₀' (by omega) hpd (HilbertModular.isIntegral_stdLat _)
    (tamagawaNumberTwo_of_complement _ hpd hn hloc hIH) (hIH Q₀' hpd')

end Main

end QuadFormsKB.Tamagawa
