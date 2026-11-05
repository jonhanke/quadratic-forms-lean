/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoNFTransport
import QuadFormsKB.Tamagawa.LocalZeta
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicSeries

/-!
# Paper 6, Theorem 5.4 at $F_{\mathfrak p} = \mathbb Q_2$ of a number field: invariance of $\beta$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, p. 23-24.

For primes $\mathfrak p$, $\mathfrak p'$ (of two number fields) with $N\mathfrak p = N\mathfrak p' = 2$ and
$2 \notin \mathfrak p^2$, $2 \notin \mathfrak p'^2$ (`IsQ2Prime`), and *any* ring isomorphism
$\sigma : \mathfrak o_{\mathfrak p} \cong \mathfrak o_{\mathfrak p'}$, Hanke's density $\beta$ is preserved by
$\sigma_*$ on nondegenerate local genera (`beta_locMap`).  *Proof:* by the comparison $\beta(\mathfrak o^n,\tfrac12H_T) =
\|2\|^{n(n-1)/2}\alpha_\pi(T,T)$ (`Hanke2005.hankeBeta_std_hessian`), with $\|2\| = \tfrac12$ on both sides, and the
representation counts $A_{\pi^k}(T,T)$ mod $\pi^k$ are preserved by a ring isomorphism carrying $(\pi^k)$ to $(\pi'^k)$
(`repCountForm_map`).  As a consequence the normalized mass sums of the true local genera satisfy
$A^*_{\mathfrak p;n}(S) = \beta(G_0)\,R^+_{\mathfrak p}(S)$-type factorizations which are transported
(`sumInvBeta_transport`).
-/

open IsDedekindDomain NumberField Matrix QuadFormsKB.Siegel QuadFormsKB.Lattices

namespace QuadFormsKB.Hanke2011Structure.RatTwoNF

noncomputable section

/-! ### Counts mod $\pi^k$ under a ring isomorphism of DVRs -/

section DVRCount

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR

variable {R R' : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] {n r : ℕ}

theorem map_eq_map_iff {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    {m : ℕ} (Q Q' : QuadForm A m) : Q.map f = Q'.map f ↔ Q = Q' := by
  constructor
  · intro h
    ext i j
    have := congrArg (fun P : QuadForm B m => P.coeff i j) h
    exact hf this
  · rintro rfl; rfl

/-- **Representation counts mod $\pi^k$ are preserved by a ring isomorphism** carrying $(\pi^k)$ to $(\pi'^k)$. -/
theorem repCountForm_map (σ : R ≃+* R') (π : R) (π' : R')
    (hπ : ∀ k : ℕ, Ideal.span {π' ^ k} = Ideal.map (σ : R →+* R') (Ideal.span {π ^ k}))
    (Q : QuadForm R n) (T : QuadForm R r) (k : ℕ) :
    repCountForm (Q.map (σ : R →+* R')) (T.map (σ : R →+* R')) π' k = repCountForm Q T π k := by
  unfold repCountForm
  set e := Ideal.quotientEquiv (Ideal.span {π ^ k}) (Ideal.span {π' ^ k}) σ (hπ k) with he
  have hcomp : (e : R ⧸ Ideal.span {π ^ k} →+* R' ⧸ Ideal.span {π' ^ k}).comp (Ideal.Quotient.mk _) =
      (Ideal.Quotient.mk _).comp (σ : R →+* R') := RingHom.ext fun x => rfl
  have key : ∀ X : Matrix (Fin n) (Fin r) (R ⧸ Ideal.span {π ^ k}),
      ((((Q.map (σ : R →+* R')).map (Ideal.Quotient.mk (Ideal.span {π' ^ k}))).compMat
          (X.map (e : R ⧸ Ideal.span {π ^ k} →+* R' ⧸ Ideal.span {π' ^ k})) =
        (T.map (σ : R →+* R')).map (Ideal.Quotient.mk (Ideal.span {π' ^ k}))) ↔
      ((Q.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).compMat X =
        T.map (Ideal.Quotient.mk (Ideal.span {π ^ k})))) := by
    intro X
    have hQ : (Q.map (σ : R →+* R')).map (Ideal.Quotient.mk (Ideal.span {π' ^ k})) =
        (Q.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).map
          (e : R ⧸ Ideal.span {π ^ k} →+* R' ⧸ Ideal.span {π' ^ k}) := by
      rw [QuadForm.map_map, QuadForm.map_map, hcomp]
    have hT : (T.map (σ : R →+* R')).map (Ideal.Quotient.mk (Ideal.span {π' ^ k})) =
        (T.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).map
          (e : R ⧸ Ideal.span {π ^ k} →+* R' ⧸ Ideal.span {π' ^ k}) := by
      rw [QuadForm.map_map, QuadForm.map_map, hcomp]
    rw [hQ, hT, QuadForm.map_compMat]
    exact map_eq_map_iff (e : R ⧸ Ideal.span {π ^ k} →+* R' ⧸ Ideal.span {π' ^ k}) e.injective _ _
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => e.toEquiv)
    (fun X => (key X).symm)).symm

theorem localDensityForm_map (σ : R ≃+* R') (π : R) (π' : R')
    (hπ : ∀ k : ℕ, Ideal.span {π' ^ k} = Ideal.map (σ : R →+* R') (Ideal.span {π ^ k}))
    (hq : DVR.q R = DVR.q R') (Q : QuadForm R n) (T : QuadForm R r) :
    localDensityForm (Q.map (σ : R →+* R')) (T.map (σ : R →+* R')) π' = localDensityForm Q T π := by
  unfold localDensityForm
  congr 1
  funext k
  rw [repCountForm_map σ π π' hπ, hq]

theorem siegelDensity_map (σ : R ≃+* R') (π : R) (π' : R')
    (hπ : ∀ k : ℕ, Ideal.span {π' ^ k} = Ideal.map (σ : R →+* R') (Ideal.span {π ^ k}))
    (hq : DVR.q R = DVR.q R') (Q : QuadForm R n) (T : QuadForm R r) :
    siegelDensity (Q.map (σ : R →+* R')) (T.map (σ : R →+* R')) π' = siegelDensity Q T π := by
  unfold siegelDensity
  rw [localDensityForm_map σ π π' hπ hq]

end DVRCount

/-! ### The primes with $N\mathfrak p = 2$, $2 \notin \mathfrak p^2$ -/

section NF

variable {F F' : Type} [Field F] [NumberField F] [Field F'] [NumberField F']
  {v : HeightOneSpectrum (𝓞 F)} {v' : HeightOneSpectrum (𝓞 F')} {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "Fw" => v'.adicCompletion F'
local notation "𝔮" => v'.adicCompletionIntegers F'

theorem IsQ2Prime.span_pi_pow (h : IsQ2Prime v) (k : ℕ) :
    Ideal.span {LocalDensity.NF.π v ^ k} = Ideal.span {(2 : 𝔬) ^ k} := by
  rw [← Ideal.span_singleton_pow, ← (LocalDensity.NF.irreducible_π v).maximalIdeal_eq, h.maximalIdeal_eq,
    Ideal.span_singleton_pow]

theorem map_span_two_pow (σ : 𝔬 ≃+* 𝔮) (k : ℕ) :
    Ideal.map (σ : 𝔬 →+* 𝔮) (Ideal.span {(2 : 𝔬) ^ k}) = Ideal.span {(2 : 𝔮) ^ k} := by
  rw [Ideal.map_span, Set.image_singleton]
  have : σ (2 : 𝔬) = 2 := map_ofNat σ 2
  simp [this]

theorem IsQ2Prime.pi_span (h : IsQ2Prime v) (h' : IsQ2Prime v') (σ : 𝔬 ≃+* 𝔮) (k : ℕ) :
    Ideal.span {LocalDensity.NF.π v' ^ k} =
      Ideal.map (σ : 𝔬 →+* 𝔮) (Ideal.span {LocalDensity.NF.π v ^ k}) := by
  rw [h.span_pi_pow, h'.span_pi_pow, map_span_two_pow]

theorem IsQ2Prime.q_eq (h : IsQ2Prime v) : LocalDensity.DVR.q 𝔬 = 2 := by
  rw [LocalDensity.NF.q_completion, h.absNorm_eq]

theorem IsQ2Prime.valued_two (h : IsQ2Prime v) : Valued.v (2 : Fv) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨u, hu⟩ := h.associated
  have h2 : (2 : Fv) = ((LocalDensity.NF.π v * (u : 𝔬) : 𝔬) : Fv) := by
    rw [hu]; exact (map_ofNat (algebraMap 𝔬 Fv) 2).symm
  rw [h2, Subring.coe_mul, map_mul, LocalDensity.NF.valued_π,
    (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1 u.isUnit, mul_one]

/-- $\lVert 2\rVert_{\mathfrak p} = \tfrac12$ when $N\mathfrak p = 2$ and $2 \notin \mathfrak p^2$. -/
theorem IsQ2Prime.norm_two (h : IsQ2Prime v) : ‖(2 : Fv)‖ = 1 / 2 := by
  rw [LocalZeta.norm_eq_absNorm_pow v two_ne_zero, h.valued_two, WithZero.log_exp, h.absNorm_eq]
  simp

/-- **Hanke's density by the Siegel density at a prime with $N\mathfrak p = 2$, $2\notin\mathfrak p^2$**:
$\beta(T) = 2^{-n(n-1)/2}\alpha_\pi(T,T)$ for nondegenerate $T$. -/
theorem IsQ2Prime.betaForm_eq (h : IsQ2Prime v) (T : QuadForm 𝔬 n) (hT : T.hessian.det ≠ 0) :
    betaForm T = (1 / 2 : ℝ) ^ (n * (n - 1) / 2) * LocalDensity.DVR.siegelDensity T T (LocalDensity.NF.π v) := by
  unfold betaForm
  rw [Hanke2005.hankeBeta_std_hessian v T hT, h.norm_two]

/-- **Hanke's density $\beta$ is preserved by $\sigma_*$ on nondegenerate local genera.** -/
theorem beta_locMap (h : IsQ2Prime v) (h' : IsQ2Prime v') (σ : 𝔬 ≃+* 𝔮) (G : LocGenus v n) (hG : G.Nondeg) :
    (locMap σ G).beta = G.beta := by
  induction G using Quotient.inductionOn with
  | _ T =>
    change (locMap σ (LocGenus.mk T)).beta = (LocGenus.mk T).beta
    have hT : T.hessian.det ≠ 0 := hG
    have hT' : (T.map (σ : 𝔬 →+* 𝔮)).hessian.det ≠ 0 := by
      rw [hessian_det_map]; exact (map_ne_zero_iff _ σ.injective).2 hT
    rw [locMap_mk, LocGenus.beta_mk, LocGenus.beta_mk, h.betaForm_eq T hT, h'.betaForm_eq _ hT',
      siegelDensity_map σ (LocalDensity.NF.π v) (LocalDensity.NF.π v') (h.pi_span h' σ)
        (by rw [h.q_eq, h'.q_eq]) T T]

/-- **The sum $\sum \beta(G)^{-1}$ over $G \in \mathrm{Gen}^*_{\mathfrak p}(S,\varepsilon;n)$** (the part of the normalized mass sum
that does not depend on the reference genus $G_0$). -/
def invBetaSum (v₀ : HeightOneSpectrum (𝓞 F)) (n : ℕ) (S : LocalSqCl v₀) (ε : ℤ) : ℝ :=
  ∑ᶠ G ∈ {G : LocGenus v₀ n | G.IsGenStar S ε}, G.beta⁻¹

/-- **Transport of the inverse-density sums**: $\sum_{G \in \mathrm{Gen}^*(S,\varepsilon)}\beta(G)^{-1}$ is the same at
$\mathfrak p$ and $\mathfrak p'$, with $S \mapsto \hat\sigma S$. -/
theorem invBetaSum_transport (h : IsQ2Prime v) (h' : IsQ2Prime v') (σ : 𝔬 ≃+* 𝔮) (S : LocalSqCl v) (ε : ℤ) :
    invBetaSum v n S ε = invBetaSum v' n (sqMap σ S) ε := by
  unfold invBetaSum
  refine finsum_mem_eq_of_bijOn (locMap σ) ⟨?_, ?_, ?_⟩ ?_
  · intro G hG
    exact (isGenStar_locMap σ S ε G).2 hG
  · exact (locMap σ).injective.injOn
  · intro G' hG'
    refine ⟨(locMap σ).symm G', ?_, (locMap σ).apply_symm_apply G'⟩
    apply (isGenStar_locMap σ S ε _).1
    simpa using hG'
  · intro G hG
    obtain ⟨hn, -⟩ := hG
    rw [beta_locMap h h' σ G hn]

/-- The normalized mass sum is $\beta(G_0)$ times the inverse-density sums. -/
theorem trueAstarNF_eq_mul (G₀ : LocGenus v n) (S : LocalSqCl v) :
    RatND.trueAstarNF v n G₀ S = G₀.beta * (invBetaSum v n S 1 + invBetaSum v n S (-1)) := by
  unfold RatND.trueAstarNF invBetaSum
  simp only [div_eq_mul_inv]
  rw [mul_add, mul_finsum_mem, mul_finsum_mem]

theorem trueBstarNF_eq_mul (G₀ : LocGenus v n) (S : LocalSqCl v) :
    RatND.trueBstarNF v n G₀ S = G₀.beta * (invBetaSum v n S 1 - invBetaSum v n S (-1)) := by
  unfold RatND.trueBstarNF invBetaSum
  simp only [div_eq_mul_inv]
  rw [mul_sub, mul_finsum_mem, mul_finsum_mem]

end NF

end

end QuadFormsKB.Hanke2011Structure.RatTwoNF

#print axioms QuadFormsKB.Hanke2011Structure.RatTwoNF.beta_locMap
#print axioms QuadFormsKB.Hanke2011Structure.RatTwoNF.invBetaSum_transport
