/-
# Shimura 1999, Lemma 2.4(4): the proper classes and $F^\times_{\mathbb A}/F^\times\sigma(D)$

Continuation of `Hanke2005/SpinorIdele.lean` (which defines $\sigma(G_w)$, $\sigma(D_v)$, $\sigma(D)$, $F^\times\sigma(D)$ and the
spinor norm $SO(V)(\mathbb A_f)\to F^\times_{\mathbb A}/F^\times\sigma(D)$, `spinorIdeleHom`).

**Proves** (for $L = \mathcal O_F^n$, $Q_0$ nondegenerate, $n\ge3$; indefinite where $\Gamma_fK$ is used)
* `isSquare_of_mem_sigmaInf`, `mem_sigmaInf_of_isotropic`: Shimura's Lemma 2.2(1) at the infinite places
  ($\sigma(G_w) = F_w^{\times2}$ where $V_w$ is anisotropic, all of $F_w^\times/F_w^{\times2}$ where it is isotropic);
* `ker_spinorIdeleHom`: $\ker\sigma = \Gamma_fK = SO(V)(F)SO(\hat L)$ (Shimura's Lemma 2.4(2) with $y = 1$). Proof as
  Shimura's: $\sigma(b)\equiv a\in F^\times$ forces $a_w\in\sigma(G_w)$, so $a = \sigma(\alpha)$ with $\alpha\in SO(V)(F)$ (his Lemma
  2.2(3); here O'Meara 101:8, `exists_evalIn_eq_mul_of_isSquare`), and $\alpha^{-1}b\in O'(V_{\mathbb A_f})SO(\hat L)$, which lies in
  $\Gamma_fK$ by strong approximation (his Lemma 2.4(1), `spinorKernel_le_classSub`);
* `exists_isSquare_div`, `unit_mem_sigmaFin`, `spinorIdeleHom_surjective`: surjectivity (Shimura: $\sigma(G_{\mathbb A}) = W$,
  $F^\times W = F^\times_{\mathbb A}$), via Mathlib's weak approximation `InfiniteAdeleRing.denseRange_algebraMap` and the local
  surjectivity `exists_so_spinorNorm_local`;
* **`shimuraLemma24_4`** (group isomorphism), **`dcEquivIdele`**, `dcEquivIdele_mk` (the bijection
  $G\backslash G_{\mathbb A}/D\to F^\times_{\mathbb A}/F^\times\sigma(D)$, $x\mapsto\sigma(x)$) and `card_DC_eq_index_idele`
  ($h = [F^\times_{\mathbb A}:F^\times\sigma(D)]$).

All unconditional, standard axioms only.
-/
import QuadFormsKB.Literature.Hanke2005.SpinorIdele

open NumberField IsDedekindDomain Matrix
open QuadFormsKB.OMeara (ideleAt ideleAtInf ideleAt_mul ideleAt_one ideleAt_inv ideleAtInf_mul ideleAtInf_one
  ideleAtInf_inv)

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005.SpinorIdele

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005.EqualMasses

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "J" => IdeleGroup (𝓞 F) F

attribute [local instance] charZero_completion

/-! ### Base change of rational rotations to any completion -/

section BaseChange

variable (Q : QuadForm F n) (K : Type*) [Field K] [Algebra F K] [CharZero K]

theorem evalIn_algebraMap (x : Fin n → F) :
    Q.evalIn K (fun i => algebraMap F K (x i)) = algebraMap F K (Q.evalIn F x) := by
  simpa using evalIn_map_tower Q K (K := F) x

/-- $(\tau_x)_K = \tau_{x_K}$ for a rational vector $x$ (any field $K\supseteq F$ of characteristic $0$). -/
theorem orthMap_symm_gen (x : Fin n → F) :
    orthMap Q K (symm Q F x) = symm Q K (fun i => algebraMap F K (x i)) := by
  have hval := evalIn_algebraMap Q K x
  by_cases hx : Q.evalIn F x ≠ 0
  · have hx' : Q.evalIn K (fun i => algebraMap F K (x i)) ≠ 0 := by
      rw [hval]; exact (map_ne_zero _).mpr hx
    ext1; ext1
    change ((symm Q F x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map (algebraMap F K) = _
    rw [symm_val Q F hx, symm_val Q K hx']
    ext i j
    simp only [QuadForm.reflMat, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply,
      symmVec, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, hval]
    split_ifs <;> simp [map_sum, map_mul, map_inv₀, map_sub]
  · have hx0 : Q.evalIn F x = 0 := not_not.mp hx
    have hx0' : Q.evalIn K (fun i => algebraMap F K (x i)) = 0 := by rw [hval, hx0, map_zero]
    have h1 : symm Q F x = 1 := by ext1; simp [Lattices.symm, symmGL_of_eq_zero Q F hx0]
    have h2 : symm Q K (fun i => algebraMap F K (x i)) = 1 := by
      ext1; simp [Lattices.symm, symmGL_of_eq_zero Q K hx0']
    rw [h1, h2, map_one]

/-- $\sigma\big((\tau_{x_1}\cdots\tau_{x_r})_K\big) = Q(x_1)\cdots Q(x_r)\,K^{\times2}$. -/
theorem spinorNorm_orthMap_symmProd (hQ : Q.Nondegenerate) (xs : List (Fin n → F))
    (hxs : ∀ x ∈ xs, Q.evalIn F x ≠ 0) :
    spinorNorm Q K (orthMap Q K (symmProd Q F xs)) = sqClassOf (algebraMap F K (valProd Q F xs)) := by
  have e : orthMap Q K (symmProd Q F xs) = symmProd Q K (xs.map fun x i => algebraMap F K (x i)) := by
    simp only [symmProd, map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => orthMap_symm_gen Q K x
  have hys : ∀ y ∈ xs.map (fun x i => algebraMap F K (x i)), Q.evalIn K y ≠ 0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    rw [evalIn_algebraMap]; exact (map_ne_zero _).mpr (hxs x hx)
  rw [e, spinorNorm_symmProd Q K hQ _ hys, valProd_map_algebraMap]

/-- Rational rotations are rotations over $K$. -/
theorem orthMap_mem_soSub {γ : orthGroup Q F} (hγ : γ ∈ soSub Q F) : orthMap Q K γ ∈ soSub Q K := by
  rw [mem_soSub]
  change ((γ : GL (Fin n) F).val.map (algebraMap F K)).det = 1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, show (γ : GL (Fin n) F).val.det = 1 from hγ, map_one]

end BaseChange

section Arch

variable (Q : QuadForm F n) (hQ : Q.Nondegenerate)

/-- **At an anisotropic archimedean place $\sigma(G_w)$ is trivial** (Shimura 1999, Lemma 2.2(1) for $v\in\mathbf c$: $G_w$ is
compact and $\sigma(G_w) = W\cap F_w^\times = F_w^{\times2}$): if $Q$ is anisotropic over $F_w$ and $cF_w^{\times2}\in\sigma(SO(V)(F_w))$,
then $c$ is a square. (A rotation is a product of an even number of symmetries, and $Q(x)Q(y)\in F_w^{\times2}$ on a
definite space, `isotropicIn_or_isSquare_mul`.) -/
@[kb "shimura1999" "Lemma 2.2(1), p. 7 (v ∈ c: σ(G_v) = F_v^{×2})"]
theorem isSquare_of_mem_sigmaInf {w : InfinitePlace F} (hiso : ¬ Q.IsotropicIn w.Completion)
    {c : w.Completion} (hc : c ≠ 0) (h : sqClassOf c ∈ sigmaInf Q hQ w) : IsSquare c := by
  obtain ⟨g, hg, hgc⟩ := (mem_sigmaInf Q hQ).mp h
  obtain ⟨zs, hzs, rfl⟩ := exists_symmProd_eq Q w.Completion hQ g
  have hdet := detHom_symmProd Q w.Completion zs hzs
  have hev : Even zs.length := by
    have h1 : ((detHom Q w.Completion (symmProd Q w.Completion zs) : w.Completion)) = 1 := hg
    rw [hdet] at h1
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h1
  have hK := (isotropicIn_or_isSquare_mul Q w).resolve_left hiso
  have hsq := isSquare_valProd_of_even Q w.Completion hK zs hzs hev
  rw [spinorNorm_symmProd Q w.Completion hQ zs hzs] at hgc
  have h1 : sqClassOf (valProd Q w.Completion zs) = 1 :=
    (sqClassOf_eq_one_iff (valProd_ne_zero Q _ hzs)).mpr hsq
  exact isSquare_of_sqClassOf_eq_one hc (by rw [← hgc, h1])

/-- **At an isotropic place every class is a spinor norm** (Shimura 1999, Lemma 2.2(1), isotropic places). -/
@[kb "shimura1999" "Lemma 2.2(1), p. 7 (isotropic places)"]
theorem mem_sigmaInf_of_isotropic {w : InfinitePlace F} (hiso : Q.IsotropicIn w.Completion)
    (c : SqClass w.Completion) : c ∈ sigmaInf Q hQ w := by
  induction c using SqClass.ind with
  | h x =>
    obtain ⟨g, hg, hgc⟩ := exists_so_spinorNorm_of_isotropic Q w.Completion hQ hiso x.ne_zero
    exact (mem_sigmaInf Q hQ).mpr ⟨g, hg, by rw [hgc, sqClassOf_of_ne_zero x.ne_zero, Units.mk0_val]⟩

end Arch

/-! ### Shimura's Lemma 2.4(4) -/

section Main

variable (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

theorem mem_stdStab_of_mem_KSO {k : SOAf Q₀} (hk : k ∈ KSO Q₀) (v : HeightOneSpectrum (𝓞 F)) :
    (k : OAf QF) v ∈ stdStab QF v := by
  have hk' : (k : OAf QF) ∈ locStab QF (stdLat F n) := Subgroup.mem_subgroupOf.mp hk
  have := hk' v
  rw [show loc v (stdLat F n).1 = std v from loc_intVec v] at this
  exact this

theorem mem_KSO_of_mem_stdStab {k : SOAf Q₀} (hk : ∀ v, (k : OAf QF) v ∈ stdStab QF v) : k ∈ KSO Q₀ := by
  refine Subgroup.mem_subgroupOf.mpr fun v => ?_
  change locAct v _ (loc v (stdLat F n).1) = loc v (stdLat F n).1
  rw [show loc v (stdLat F n).1 = std v from loc_intVec v]
  exact hk v

/-- $\sigma(SO(V)(F))\subseteq F^\times$: rational rotations have principal spinor norm. -/
theorem spinorIdeleHom_finHom (γs : soSub QF F) :
    spinorIdeleHom QF (nondegenerate_map Q₀ hQ) (finHom Q₀ γs) = 1 := by
  have hQF := nondegenerate_map Q₀ hQ
  obtain ⟨xs, hxs, hxe⟩ := exists_symmProd_eq QF F hQF (γs : orthGroup QF F)
  set a : Fˣ := Units.mk0 (valProd QF F xs) (valProd_ne_zero QF F hxs)
  rw [spinorIdeleHom_eq QF hQF (x := IdeleGroup.unitEmbedding (𝓞 F) F a)]
  · rw [QuotientGroup.eq_one_iff]; exact Subgroup.mem_sup_left ⟨a, rfl⟩
  · refine ⟨fun w => ?_, fun v => ?_⟩
    · rw [ideleAtInf_unitEmbedding, mem_sigmaInf]
      refine ⟨orthMap QF w.Completion γs, orthMap_mem_soSub QF w.Completion γs.2, ?_⟩
      rw [← hxe, spinorNorm_orthMap_symmProd QF w.Completion hQF xs hxs]
      rfl
    · have e : ((finHom Q₀ γs : soAf QF) : OAf QF) v = orthMap QF (v.adicCompletion F) γs := rfl
      rw [e, ideleAt_unitEmbedding, ← hxe, spinorNorm_orthMap_symmProd QF _ hQF xs hxs]
      simp only [a, Units.val_mk0]
      rw [SqClass.mul_self]
      exact Subgroup.one_mem _

/-- $\sigma(SO(\hat L))\subseteq\sigma(D)$. -/
theorem spinorIdeleHom_KSO {k : SOAf Q₀} (hk : k ∈ KSO Q₀) :
    spinorIdeleHom QF (nondegenerate_map Q₀ hQ) k = 1 := by
  have hQF := nondegenerate_map Q₀ hQ
  rw [spinorIdeleHom_eq QF hQF (x := 1), QuotientGroup.mk_one]
  refine ⟨fun w => ?_, fun v => ?_⟩
  · rw [ideleAtInf_one, sqClassOf_one]; exact Subgroup.one_mem _
  · rw [ideleAt_one, sqClassOf_one, one_mul, mem_sigmaFin]
    exact ⟨_, ⟨mem_stdStab_of_mem_KSO Q₀ hk v, k.2 v⟩, rfl⟩

/-- **The kernel of the spinor norm contains $\Gamma_fK$.** -/
theorem classSub_le_ker (hn : 3 ≤ n) (hind : IsIndefinite QF) :
    classSub Q₀ hn hQ hind ≤ (spinorIdeleHom QF (nondegenerate_map Q₀ hQ)).ker := by
  rintro b ⟨γ, ⟨γs, rfl⟩, k, hk, rfl⟩
  rw [MonoidHom.mem_ker, map_mul]
  have e : (diagSOAdele Q₀ γs).2 = finHom Q₀ γs := rfl
  rw [e, spinorIdeleHom_finHom Q₀ hQ, spinorIdeleHom_KSO Q₀ hQ hk]
  exact mul_one (1 : J ⧸ classIdeleSub QF (nondegenerate_map Q₀ hQ))

/-- **The kernel of the spinor norm is contained in $\Gamma_fK$** (Shimura 1999, proofs of Lemmas 2.3(2) and 2.4: if
$\sigma(x)\equiv a$ with $a\in F^\times$, then $a\in W\cap F^\times$, $a = \sigma(\alpha)$ with $\alpha\in G$ (Lemma 2.2(3)), and
$\alpha^{-1}x\in G^0_{\mathbb A}D\subseteq G^0D$ (Lemma 2.4(1), strong approximation)). -/
theorem ker_le_classSub (hn : 3 ≤ n) (hind : IsIndefinite QF) :
    (spinorIdeleHom QF (nondegenerate_map Q₀ hQ)).ker ≤ classSub Q₀ hn hQ hind := by
  classical
  have hQF := nondegenerate_map Q₀ hQ
  intro b hb
  rw [MonoidHom.mem_ker] at hb
  obtain ⟨x, hx⟩ := exists_spinorRel QF hQF b
  rw [spinorIdeleHom_eq QF hQF hx, QuotientGroup.eq_one_iff] at hb
  obtain ⟨p, ⟨α, rfl⟩, s, hs, hps⟩ := Subgroup.mem_sup.mp hb
  -- `p = (α)` represents `σ(b)`
  have hp : SpinorRel QF hQF b (IdeleGroup.unitEmbedding (𝓞 F) F α) := by
    have h1 := spinorRel_mul QF hQF hx ((spinorRel_one_iff QF hQF s⁻¹).mpr ((sigmaD QF hQF).inv_mem hs))
    rw [mul_one, ← hps, mul_inv_cancel_right] at h1
    exact h1
  -- a global rotation `α' = τ_x τ_y` with `σ(α') = α` (Shimura's Lemma 2.2(3), O'Meara 101:8)
  have hinf : ∀ w : InfinitePlace F, (QF).IsotropicIn w.Completion ∨
      IsSquare (algebraMap F w.Completion (α : F)) := by
    intro w
    by_cases hiso : (QF).IsotropicIn w.Completion
    · exact Or.inl hiso
    · right
      have := hp.1 w
      rw [ideleAtInf_unitEmbedding] at this
      exact isSquare_of_mem_sigmaInf QF hQF hiso ((map_ne_zero _).mpr α.ne_zero) this
  obtain ⟨x0, y0, hy0, hxy⟩ := exists_evalIn_eq_mul_of_isSquare QF hQF hn α.ne_zero hinf
  have hx0 : (QF).evalIn F x0 ≠ 0 := by rw [hxy]; exact mul_ne_zero α.ne_zero hy0
  set α' : orthGroup QF F := symm QF F x0 * symm QF F y0
  have hα'so : α' ∈ soSub QF F := by
    rw [mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul, symm_det QF F hx0, symm_det QF F hy0]
    norm_num
  set γs : soSub QF F := ⟨α', hα'so⟩
  have hσα : ∀ v : HeightOneSpectrum (𝓞 F), spinorNorm QF (v.adicCompletion F) (orthMap QF _ α') =
      sqClassOf (algebraMap F (v.adicCompletion F) (α : F)) := by
    intro v
    rw [spinorNorm_orthMap_symm_mul QF hQF v hx0 hy0, hxy, map_mul, map_mul]
    have hyv : algebraMap F (v.adicCompletion F) ((QF).evalIn F y0) ≠ 0 := (map_ne_zero _).mpr hy0
    have hav : algebraMap F (v.adicCompletion F) (α : F) ≠ 0 := (map_ne_zero _).mpr α.ne_zero
    rw [mul_assoc, sqClassOf_mul hav (mul_ne_zero hyv hyv),
      (sqClassOf_eq_one_iff (mul_ne_zero hyv hyv)).mpr ⟨_, rfl⟩, mul_one]
  -- `b' = α'⁻¹ b` has `σ(b'_v) ∈ σ(SO(L_v))` at every `v`
  set b' : SOAf Q₀ := (finHom Q₀ γs)⁻¹ * b
  have hb'v : ∀ v, (b' : OAf QF) v = (orthMap QF (v.adicCompletion F) α')⁻¹ * (b : OAf QF) v := fun v => rfl
  have hσb' : ∀ v, spinorNorm QF (v.adicCompletion F) ((b' : OAf QF) v) ∈ sigmaFin QF hQF v := by
    intro v
    have := hp.2 v
    rw [ideleAt_unitEmbedding] at this
    rw [hb'v, ← spinorNormHom_apply QF _ hQF, map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hσα,
      SqClass.inv_eq]
    exact this
  -- local factors `k_v ∈ SO(L_v)` with `σ(k_v) = σ(b'_v)`, equal to `b'_v` when `b'_v ∈ SO(L_v)`
  have hk : ∀ v, ∃ k ∈ stdStab QF v ⊓ soSub QF (v.adicCompletion F),
      spinorNorm QF (v.adicCompletion F) k = spinorNorm QF (v.adicCompletion F) ((b' : OAf QF) v) ∧
      ((b' : OAf QF) v ∈ stdStab QF v → k = (b' : OAf QF) v) := by
    intro v
    by_cases hv : (b' : OAf QF) v ∈ stdStab QF v
    · exact ⟨_, ⟨hv, b'.2 v⟩, rfl, fun _ => rfl⟩
    · obtain ⟨k, hk, hkσ⟩ := (mem_sigmaFin QF hQF).mp (hσb' v)
      exact ⟨k, hk, hkσ, fun h => absurd h hv⟩
  choose kk hkk hkkσ hkkeq using hk
  -- `c_v = b'_v k_v⁻¹ ∈ O'(V_v)`
  let c : OAf QF := ⟨fun v => (b' : OAf QF) v * (kk v)⁻¹, by
    filter_upwards [(b' : OAf QF).2] with v hv
    change (b' : OAf QF) v * (kk v)⁻¹ ∈ stdStab QF v
    rw [hkkeq v hv, mul_inv_cancel]
    exact (stdStab QF v).one_mem⟩
  have hcv : ∀ v, c v = (b' : OAf QF) v * (kk v)⁻¹ := fun v => rfl
  have hcso : c ∈ soAf QF := fun v => by
    rw [hcv]; exact (soSub QF _).mul_mem (b'.2 v) ((soSub QF _).inv_mem (hkk v).2)
  have hcker : c ∈ spinorKernelAf QF := by
    intro v
    rw [hcv, spinorKernel_eq_ker QF _ hQF]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hkkσ, mul_inv_cancel]
    · rw [MonoidHom.mem_ker, map_mul, map_inv]
      have h1 : detHom QF (v.adicCompletion F) ((b' : OAf QF) v) = 1 := Units.ext (b'.2 v)
      have h2 : detHom QF (v.adicCompletion F) (kk v) = 1 := Units.ext (hkk v).2
      rw [h1, h2, inv_one, mul_one]
  set cs : SOAf Q₀ := ⟨c, hcso⟩
  set ks : SOAf Q₀ := cs⁻¹ * b'
  have hks : ks ∈ KSO Q₀ := by
    refine mem_KSO_of_mem_stdStab Q₀ fun v => ?_
    have : (ks : OAf QF) v = kk v := by
      change (c v)⁻¹ * (b' : OAf QF) v = kk v
      rw [hcv]; group
    rw [this]; exact (hkk v).1
  have hb : b = finHom Q₀ γs * cs * ks := by simp only [ks, b']; group
  rw [hb]
  refine (classSub Q₀ hn hQ hind).mul_mem ((classSub Q₀ hn hQ hind).mul_mem ?_ ?_) ?_
  · exact ⟨diagSOAdele Q₀ γs, ⟨γs, rfl⟩, 1, (KSO Q₀).one_mem, by rw [mul_one]; rfl⟩
  · exact spinorKernel_le_classSub Q₀ hn hQ hind cs hcker
  · exact ⟨1, (GammaSOAdele Q₀).one_mem, ks, hks, by simp⟩

/-- **$\ker\sigma = \Gamma_fK$**: the kernel of $SO(V)(\mathbb A_f)\to F^\times_{\mathbb A}/F^\times\sigma(D)$ is $SO(V)(F)\,SO(\hat L)$
(Shimura 1999, Lemma 2.4(2) with $y = 1$: $GD = \{x\in G_{\mathbb A} : \sigma(x)\in F^\times\sigma(D)\}$). -/
@[kb "shimura1999" "Lemma 2.4(2), p. 8 (GD = {x : σ(x) ∈ F^×σ(D)})"]
theorem ker_spinorIdeleHom (hn : 3 ≤ n) (hind : IsIndefinite QF) :
    (spinorIdeleHom QF (nondegenerate_map Q₀ hQ)).ker = classSub Q₀ hn hQ hind :=
  le_antisymm (ker_le_classSub Q₀ hQ hn hind) (classSub_le_ker Q₀ hQ hn hind)

/-- **Weak approximation at the infinite places, for square classes**: for every idèle $x$ there is $a\in F^\times$ with
$x_w/a_w\in F_w^{\times2}$ at every infinite place $w$ (so $F^\times W = F^\times_{\mathbb A}$ in Shimura's notation). -/
theorem exists_isSquare_div (x : J) :
    ∃ a : Fˣ, ∀ w : InfinitePlace F, IsSquare (ideleAtInf x w / algebraMap F w.Completion (a : F)) := by
  let δ : InfinitePlace F → ℝ := fun w => ‖ideleAtInf x w‖ * min (‖(2 : w.Completion)‖ ^ 2 / 8) (1 / 2)
  have hδ : ∀ w, 0 < δ w := by
    intro w
    have h2 : (2 : w.Completion) ≠ 0 := two_ne_zero
    have h2' := norm_pos_iff.mpr h2
    exact mul_pos (norm_pos_iff.mpr (ideleAtInf_ne_zero x w)) (lt_min (by positivity) (by norm_num))
  let U : Set (InfiniteAdeleRing F) := ⋂ w, {z | ‖z w - ideleAtInf x w‖ < δ w}
  have hU : IsOpen U := isOpen_iInter_of_finite fun w =>
    isOpen_lt ((continuous_apply w).sub continuous_const).norm continuous_const
  have hxU : (fun w => ideleAtInf x w : InfiniteAdeleRing F) ∈ U :=
    Set.mem_iInter.mpr fun w => by
      show ‖ideleAtInf x w - ideleAtInf x w‖ < δ w
      rw [sub_self, norm_zero]; exact hδ w
  obtain ⟨a, ha⟩ := (InfiniteAdeleRing.denseRange_algebraMap (K := F)).exists_mem_open hU ⟨_, hxU⟩
  have hclose : ∀ w, ‖algebraMap F w.Completion a - ideleAtInf x w‖ < δ w := fun w =>
    Set.mem_iInter.mp ha w
  have hsq : ∀ w, IsSquare (algebraMap F w.Completion a / ideleAtInf x w) := by
    intro w
    have hx0 := ideleAtInf_ne_zero x w
    refine isSquare_of_norm_sub_one_lt two_ne_zero ?_
    have e : algebraMap F w.Completion a / ideleAtInf x w - 1 =
        (algebraMap F w.Completion a - ideleAtInf x w) / ideleAtInf x w := by field_simp
    rw [e, norm_div, div_lt_iff₀ (norm_pos_iff.mpr hx0)]
    calc _ < δ w := hclose w
      _ ≤ _ := by
        simp only [δ]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
  have ha0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have h := hclose w
    have hx0 := norm_pos_iff.mpr (ideleAtInf_ne_zero x w)
    rw [map_zero, zero_sub, norm_neg] at h
    have : δ w ≤ ‖ideleAtInf x w‖ * (1 / 2) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)
    linarith
  refine ⟨Units.mk0 a ha0, fun w => ?_⟩
  have := (hsq w).inv
  rwa [inv_div] at this

/-- The units are spinor norms of $SO(L_v)$ at the places $v\nmid2\det H$ (O'Meara 92:5). -/
theorem unit_mem_sigmaFin (hn : 2 ≤ n) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badPrimes Q₀)
    {u : v.adicCompletion F} (hu : Valued.v u = 1) :
    sqClassOf u ∈ sigmaFin QF (nondegenerate_map Q₀ hQ) v := by
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ h)
  have hdet : Q₀.hessian.det ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  obtain ⟨g1, hg1, hd1, hθ1⟩ := spinorNorm_stdStab_unit v Q₀ h2 hdet hn hu
  obtain ⟨g2, hg2, hd2, hθ2⟩ := spinorNorm_stdStab_unit v Q₀ h2 hdet hn (u := 1) (by simp)
  rw [mem_sigmaFin]
  refine ⟨g1 * g2, ⟨(stdStab QF v).mul_mem hg1 hg2, ?_⟩, ?_⟩
  · have : detHom QF (v.adicCompletion F) (g1 * g2) = 1 := by rw [map_mul, hd1, hd2]; norm_num
    exact congrArg Units.val this
  · rw [← spinorNormHom_apply QF _ (nondegenerate_map Q₀ hQ), map_mul, spinorNormHom_apply, spinorNormHom_apply,
      hθ1, hθ2, sqClassOf_one, mul_one]

/-- **The spinor norm $SO(V)(\mathbb A_f)\to F^\times_{\mathbb A}/F^\times\sigma(D)$ is surjective** for $n\ge3$ (Shimura 1999, proofs
of Lemmas 2.3(4) and 2.4(4): the image is $F^\times W/F^\times\sigma(D)$, with $\sigma(G_{\mathbb A}) = W$ (Lemma 2.2(2)) and
$F^\times W = F^\times_{\mathbb A}$ for $n>2$). -/
@[kb "shimura1999" "Lemma 2.2(2), p. 7 and Lemma 2.3(4), p. 8 (the image is F^×W/F^×σ(D) = F_A^×/F^×σ(D))"]
theorem spinorIdeleHom_surjective (hn : 3 ≤ n) :
    Function.Surjective (spinorIdeleHom QF (nondegenerate_map Q₀ hQ)) := by
  classical
  have hQF := nondegenerate_map Q₀ hQ
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨a, ha⟩ := exists_isSquare_div x
    set p : J := IdeleGroup.unitEmbedding (𝓞 F) F a
    set y : J := x * p⁻¹
    have hyw : ∀ w, IsSquare (ideleAtInf y w) := by
      intro w
      have e : ideleAtInf y w = ideleAtInf x w / algebraMap F w.Completion (a : F) := by
        simp only [y, p, ideleAtInf_mul, ideleAtInf_inv, ideleAtInf_unitEmbedding, div_eq_mul_inv]
      rw [e]; exact ha w
    -- local rotations
    have hg : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g ∈ soSub QF (v.adicCompletion F),
        (sqClassOf (ideleAt y v) ∈ sigmaFin QF hQF v → g = 1) ∧
        (sqClassOf (ideleAt y v) ∉ sigmaFin QF hQF v →
          spinorNorm QF (v.adicCompletion F) g = sqClassOf (ideleAt y v)) := by
      intro v
      by_cases hv : sqClassOf (ideleAt y v) ∈ sigmaFin QF hQF v
      · exact ⟨1, (soSub QF _).one_mem, fun _ => rfl, fun h => absurd hv h⟩
      · obtain ⟨g, hg, hgσ⟩ := exists_so_spinorNorm_local QF v hQF hn (ideleAt_ne_zero y v)
        exact ⟨g, hg, fun h => absurd h hv, fun _ => hgσ⟩
    choose g hgso hg1 hgσ using hg
    -- almost everywhere `σ(y_v) ∈ σ(SO(L_v))`
    have hev : ∀ᶠ v in Filter.cofinite, sqClassOf (ideleAt y v) ∈ sigmaFin QF hQF v := by
      have hunit := (NumberField.AdeleRing.isUnit_iff.mp (Units.isUnit y)).2.2
      have hbad := (finite_badPrimes Q₀ hQ).eventually_cofinite_notMem
      filter_upwards [hunit, hbad] with v hu hv
      exact unit_mem_sigmaFin Q₀ hQ (by omega) hv hu
    let b : OAf QF := ⟨g, by
      filter_upwards [hev] with v hv
      rw [hg1 v hv]; exact (stdStab QF v).one_mem⟩
    have hbso : b ∈ soAf QF := fun v => hgso v
    refine ⟨⟨b, hbso⟩, ?_⟩
    rw [spinorIdeleHom_eq QF hQF (x := y)]
    · rw [QuotientGroup.eq]
      refine Subgroup.mem_sup_left ⟨a, ?_⟩
      simp [y, p]
    · refine ⟨fun w => ?_, fun v => ?_⟩
      · rw [(sqClassOf_eq_one_iff (ideleAtInf_ne_zero y w)).mpr (hyw w)]; exact Subgroup.one_mem _
      · change sqClassOf (ideleAt y v) * spinorNorm QF _ (g v) ∈ _
        by_cases hv : sqClassOf (ideleAt y v) ∈ sigmaFin QF hQF v
        · rw [hg1 v hv, spinorNorm_one' QF hQF, mul_one]; exact hv
        · rw [hgσ v hv, SqClass.mul_self]; exact Subgroup.one_mem _

/-- **Shimura 1999, Lemma 2.4(4)** (group form): for $Q_0$ nondegenerate in $n\ge3$ variables, the spinor norm induces an
isomorphism $SO(V)(\mathbb A_f)/\ker\sigma\simeq F^\times_{\mathbb A}/F^\times\sigma(D)$; for $Q_0$ indefinite,
$\ker\sigma = SO(V)(F)\,SO(\hat L)$ (`ker_spinorIdeleHom`). -/
@[kb "shimura1999" "Lemma 2.4(4), p. 8"]
def shimuraLemma24_4 (hn : 3 ≤ n) :
    SOAf Q₀ ⧸ (spinorIdeleHom QF (nondegenerate_map Q₀ hQ)).ker ≃* J ⧸ classIdeleSub QF (nondegenerate_map Q₀ hQ) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (spinorIdeleHom_surjective Q₀ hQ hn)

/-- **Shimura 1999, Lemma 2.4(4)**: for $Q_0$ nondegenerate and indefinite in $n\ge3$ variables ($G_{\mathbf a}$ not
compact), the spinor norm $x\mapsto\sigma(x)$ defines a bijection
$$SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)\ \longrightarrow\ F^\times_{\mathbb A}/F^\times\sigma(D)$$
(`dcEquivIdele_mk`: the class of $b$ goes to the class of any idèle representing $\sigma(b)$). -/
@[kb "shimura1999" "Lemma 2.4(4), p. 8 (G\\G_A/D ≅ F_A^×/F^×σ(D) via σ)"]
def dcEquivIdele (hn : 3 ≤ n) (hind : IsIndefinite QF) :
    DC Q₀ ≃ J ⧸ classIdeleSub QF (nondegenerate_map Q₀ hQ) :=
  (dcEquivQuot Q₀ hn hQ hind).trans
    ((Subgroup.quotientEquivOfEq (ker_spinorIdeleHom Q₀ hQ hn hind).symm).trans
      (shimuraLemma24_4 Q₀ hQ hn).toEquiv)

theorem dcEquivIdele_mk (hn : 3 ≤ n) (hind : IsIndefinite QF) {b : SOAf Q₀} {x : J}
    (h : SpinorRel QF (nondegenerate_map Q₀ hQ) b x) :
    dcEquivIdele Q₀ hQ hn hind ⟦b⟧ = QuotientGroup.mk x :=
  spinorIdeleHom_eq QF (nondegenerate_map Q₀ hQ) h

/-- **The number of proper classes is an idèle index** (Shimura 1999, Lemma 2.4(4); Hanke thesis, proof of Cor. 5.2):
$h = [F^\times_{\mathbb A}:F^\times\sigma(D)]$ for $Q_0$ nondegenerate and indefinite in $n\ge3$ variables. -/
@[kb "shimura1999" "Lemma 2.4(4), p. 8 (h = [F_A^× : F^×σ(D)])"]
theorem card_DC_eq_index_idele (hn : 3 ≤ n) (hind : IsIndefinite QF) :
    Nat.card (DC Q₀) = (classIdeleSub QF (nondegenerate_map Q₀ hQ)).index := by
  rw [Subgroup.index, Nat.card_congr (dcEquivIdele Q₀ hQ hn hind)]

end Main

end QuadFormsKB.Hanke2005.SpinorIdele
