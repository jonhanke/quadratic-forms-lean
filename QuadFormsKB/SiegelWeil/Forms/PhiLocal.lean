/-
# The Weil representation and the embedding $\mathrm{Sp}_{2r} \to \mathrm{Sp}_{2r+2}$ ($\Phi E^{(r+1)} = E^{(r)}$)

**Layer:** local at a finite place $v$ of a number field $F$ (dyadic places included), unconditional.

**Setting.** $V = F_v^{2m}$ with $Q(x) = \sum_i a_ix_i^2$, $S(V^g)$ the Schwartz–Bruhat space of $V^g = M_{2m\times g}(F_v)$ and
$\omega_g = $ `weilRepSpV v a g` the Weil representation of $\mathrm{Sp}_{2g}(F_v)$ on it. The group $\mathrm{Sp}_{2r}(F_v)$ is embedded in
$\mathrm{Sp}_{2r+2}(F_v)$ by $\iota =$ `embSp` on the variables $1, \dots, r$, and $S(V^1)\otimes S(V^r) \subseteq S(V^{r+1})$
(`tensG`, columns $0$ and $1, \dots, r$).

**Results.**
* `weilRepSpV_embSp_tensG`: $\omega_{r+1}(\iota\delta)(\varphi\otimes\Phi) = \varphi\otimes\omega_r(\delta)\Phi$ for all
  $\delta \in \mathrm{Sp}_{2r}(F_v)$, $\varphi \in S(V^1)$, $\Phi \in S(V^r)$. *Proof:* both sides are compatible with products, so it suffices
  to check the generators $n(B)$, $m(A)$ (`opNg_extC`, `opMg_extGL`) and $w$. For $w$, the partial Weyl element $w_0$ in the variable $0$
  (`wEps`, $w_0 = n(\varepsilon)w^{-1}n(\varepsilon)\,w\,n(\varepsilon)$ with $\varepsilon = \mathrm{extC}\,1\,0$) satisfies
  $w = w_0\,\iota(w)$ (`spW_eq_wEps_mul`), and $\omega(w_0)(\varphi\otimes\Phi) = \omega_1(w)\varphi\otimes\Phi$ because
  $n(1)w^{-1}n(1)\,w\,n(1) = w$ in $\mathrm{Sp}_2$ (`spN_one_spW`); together with $\omega(w)(\varphi\otimes\Phi) = \omega_1(w)\varphi\otimes\omega_r(w)\Phi$
  (`opWg_tensG`) this gives $\omega(\iota w)(\varphi\otimes\Phi) = \varphi\otimes\omega_r(w)\Phi$.
* `secRV_oneSG_embSp`: for the lattice function $\mathbf 1_{L_v^{r+1}} = \mathbf 1_{L_v}\otimes\mathbf 1_{L_v^{r}}$ the section satisfies
  $f_{r+1}(\iota\delta) = f_r(\delta)$, where $f_g(h) = (\omega_g(h)\mathbf 1_{L_v^g})(0)$.

Source: Kudla, *Notes on the local theta correspondence* (1996), §I.1 [unverified]; Weil, Acta Math. 111 (1964) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.PhiTensor
import QuadFormsKB.SiegelWeil.Forms.Sections
import QuadFormsKB.SiegelWeil.Forms.EisensteinSpherical
import QuadFormsKB.Weil.Genus.SiegelTwoCell

open Matrix MeasureTheory IsDedekindDomain NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open QuadFormsKB.WeilRep QuadFormsKB.WeilRep.Genus QuadFormsKB.WeilRep.LocalData

section Mat

variable {k : Type*} [Field k] {r : ℕ}

lemma extC_neg (c : k) (X : Matrix (Fin r) (Fin r) k) : -extC c X = extC (-c) (-X) :=
  extC_ext (by simp) (by simp) (by simp) (by simp)

/-- $w^{-1} = w^3$ in $\mathrm{Sp}_{2g}(k)$. -/
lemma spW_inv {g : ℕ} : (spW : Sp g k)⁻¹ = spW * spW * spW := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp [Submonoid.coe_mul, fromBlocks_multiply]

/-- **The partial Weyl element in the variable $0$:** $w_0 = n(\varepsilon)\,w^{-1}\,n(\varepsilon)\,w\,n(\varepsilon)$, $\varepsilon = \mathrm{extC}\,1\,0$. -/
def wEps (r : ℕ) : Sp (r + 1) k :=
  spN (extC 1 0) (extC_symm (by simp) 1) * spW⁻¹ * spN (extC 1 0) (extC_symm (by simp) 1) * spW *
    spN (extC 1 0) (extC_symm (by simp) 1)

lemma wEps_coe : ((wEps r : Sp (r + 1) k) : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k) =
    fromBlocks (extC 0 1) (extC 1 0) (extC (-1) 0) (extC 0 1) := by
  rw [wEps, spW_inv]
  simp only [Submonoid.coe_mul, spN_coe, spW_coe, fromBlocks_multiply]
  rw [← extC_one (k := k) (r := r), ← extC_zero (k := k) (r := r)]
  simp [extC_mul, extC_add, extC_neg]

/-- $w = w_0\,\iota(w)$ in $\mathrm{Sp}_{2r+2}(k)$. -/
lemma spW_eq_wEps_mul : (spW : Sp (r + 1) k) = wEps r * embSp spW := by
  refine Subtype.ext ?_
  rw [Submonoid.coe_mul, wEps_coe, embSp_coe, embMat]
  simp only [spW_coe, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    fromBlocks_multiply]
  rw [← extC_one (k := k) (r := r), ← extC_zero (k := k) (r := r)]
  simp [extC_mul, extC_add, extC_neg]

/-- $n(1)\,w^{-1}\,n(1)\,w\,n(1) = w$ in $\mathrm{Sp}_{2g}(k)$. -/
lemma spN_one_spW {g : ℕ} :
    spN (1 : Matrix (Fin g) (Fin g) k) (by simp) * spW⁻¹ * spN (1 : Matrix (Fin g) (Fin g) k) (by simp) * spW *
      spN (1 : Matrix (Fin g) (Fin g) k) (by simp) = spW := by
  rw [spW_inv]
  refine Subtype.ext ?_
  simp [Submonoid.coe_mul, fromBlocks_multiply]

end Mat

section Gen

variable {K : Type*} [Field K] [MeasurableSpace K] {m r : ℕ} {D : LocalData K}

/-- The tensor product $\varphi\otimes\Phi \in S(V^{r+1})$ of $\varphi \in S(V^1)$ and $\Phi \in S(V^r)$. -/
def tensS (φ : Sg D m 1) (Φ : Sg D m r) : Sg D m (r + 1) :=
  ⟨tensG φ Φ, tensG_mem φ.2 Φ.2⟩

/-- **$T$ acts on tensor products factorwise** as $T_1 \otimes T_r$. -/
def IsTens (T : Module.End ℂ (Sg D m (r + 1))) (T1 : Module.End ℂ (Sg D m 1))
    (Tr : Module.End ℂ (Sg D m r)) : Prop :=
  ∀ (φ : Sg D m 1) (Φ : Sg D m r), ((T (tensS φ Φ) : Sg D m (r + 1)) : PtG m (r + 1) K → ℂ) =
    tensG (T1 φ) (Tr Φ)

lemma IsTens.comp {T S : Module.End ℂ (Sg D m (r + 1))} {T1 S1 : Module.End ℂ (Sg D m 1)}
    {Tr Sr : Module.End ℂ (Sg D m r)} (hT : IsTens T T1 Tr) (hS : IsTens S S1 Sr) :
    IsTens (T * S) (T1 * S1) (Tr * Sr) := by
  intro φ Φ
  have h : S (tensS φ Φ) = tensS (S1 φ) (Sr Φ) := Subtype.ext (hS φ Φ)
  rw [Module.End.mul_apply, h, hT]
  rfl

lemma IsTens.one : IsTens (1 : Module.End ℂ (Sg D m (r + 1))) 1 (1 : Module.End ℂ (Sg D m r)) :=
  fun _ _ => rfl

end Gen

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

variable {m r : ℕ}

/-- $\omega_{r+1}(g)$ acts on tensor products as $\omega_1(g_1)\otimes\omega_r(g_r)$. -/
def IsTensG (a : Fin (2 * m) → (Fv)ˣ) (g : Sp (r + 1) Fv) (g1 : Sp 1 Fv) (gr : Sp r Fv) : Prop :=
  IsTens (weilRepSpV v a (r + 1) g) (weilRepSpV v a 1 g1) (weilRepSpV v a r gr)

variable {v}

variable {a : Fin (2 * m) → (v.adicCompletion F)ˣ}

lemma IsTensG.one : IsTensG v a (1 : Sp (r + 1) Fv) (1 : Sp 1 Fv) (1 : Sp r Fv) := by
  unfold IsTensG; simp only [map_one]; exact IsTens.one

lemma IsTensG.mul {g h : Sp (r + 1) Fv} {g1 h1 : Sp 1 Fv} {gr hr : Sp r Fv} (hg : IsTensG v a g g1 gr)
    (hh : IsTensG v a h h1 hr) : IsTensG v a (g * h) (g1 * h1) (gr * hr) := by
  unfold IsTensG at *; simp only [map_mul]; exact hg.comp hh

lemma IsTensG.inv {g : Sp (r + 1) Fv} {g1 : Sp 1 Fv} {gr : Sp r Fv} (hg : IsTensG v a g g1 gr) :
    IsTensG v a g⁻¹ g1⁻¹ gr⁻¹ := by
  intro φ Φ
  have e : ∀ {n : ℕ} (h : Sp n Fv) (x : Sg (localDataV v) m n), weilRepSpV v a n h (weilRepSpV v a n h⁻¹ x) = x := by
    intro n h x
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have e' : ∀ {n : ℕ} (h : Sp n Fv) (x : Sg (localDataV v) m n), weilRepSpV v a n h⁻¹ (weilRepSpV v a n h x) = x := by
    intro n h x
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h1 : tensS φ Φ = weilRepSpV v a (r + 1) g (tensS (weilRepSpV v a 1 g1⁻¹ φ) (weilRepSpV v a r gr⁻¹ Φ)) := by
    refine Subtype.ext ?_
    rw [hg, e, e]
    rfl
  conv_lhs => rw [h1, e']
  rfl

lemma isTensG_N (B : Matrix (Fin r) (Fin r) Fv) (hB : Bᵀ = B) :
    IsTensG v a (embSp (spN B hB)) 1 (spN B hB) := by
  intro φ Φ
  have hid : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) Fv), M.map (RingHom.id Fv) = M := fun M => by ext; rfl
  rw [embSp_spN, weilRepSpV_spN, weilRepSpV_spN, endN_apply _ _ (extC_symm hB 0), endN_apply _ _ hB]
  simp only [map_one, Module.End.one_apply]
  change opNg (localDataV v) a ((extC 0 B).map (RingHom.id Fv)) (tensG φ Φ) =
    tensG φ (opNg (localDataV v) a (B.map (RingHom.id Fv)) Φ)
  rw [hid, hid, opNg_extC]
  have h0 : opNg (localDataV v) a (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (0 : Fv)) (φ : PtG m 1 Fv → ℂ) = φ := by
    funext X
    have : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (0 : Fv)) = 0 := rfl
    simp [opNg, this]
  rw [h0]

lemma isTensG_M (A : GL (Fin r) Fv) : IsTensG v a (embSp (spM A)) 1 (spM A) := by
  intro φ Φ
  have hid : ∀ {n : ℕ} (A : GL (Fin n) Fv), Matrix.GeneralLinearGroup.map (RingHom.id Fv) A = A := fun A => by
    ext; rfl
  rw [embSp_spM, weilRepSpV_spM, weilRepSpV_spM, endM_apply, endM_apply]
  simp only [map_one, Module.End.one_apply]
  change opMg (localDataV v) a (Matrix.GeneralLinearGroup.map (RingHom.id Fv) (extGL A)) (tensG φ Φ) =
    tensG φ (opMg (localDataV v) a (Matrix.GeneralLinearGroup.map (RingHom.id Fv) A) Φ)
  rw [hid, hid, opMg_extGL]

lemma isTensG_W : IsTensG v a (spW : Sp (r + 1) Fv) (spW : Sp 1 Fv) (spW : Sp r Fv) := by
  intro φ Φ
  rw [weilRepSpV_spW, weilRepSpV_spW, weilRepSpV_spW]
  exact opWg_tensG (isOps_V v) _ _

lemma isTensG_nEps : IsTensG v a (spN (extC 1 0) (extC_symm (by simp) 1) : Sp (r + 1) Fv)
    (spN (1 : Matrix (Fin 1) (Fin 1) Fv) (by simp)) 1 := by
  intro φ Φ
  have hid : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) Fv), M.map (RingHom.id Fv) = M := fun M => by ext; rfl
  rw [weilRepSpV_spN, weilRepSpV_spN, endN_apply _ _ (B := extC 1 0) (extC_symm (by simp) 1),
    endN_apply _ _ (B := (1 : Matrix (Fin 1) (Fin 1) Fv)) (by simp)]
  simp only [map_one, Module.End.one_apply]
  change opNg (localDataV v) a ((extC 1 0).map (RingHom.id Fv)) (tensG φ Φ) =
    tensG (opNg (localDataV v) a ((1 : Matrix (Fin 1) (Fin 1) Fv).map (RingHom.id Fv)) φ) (Φ : PtG m r Fv → ℂ)
  have h1 : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (1 : Fv)) = (1 : Matrix (Fin 1) (Fin 1) Fv) := by
    ext i j
    fin_cases i; fin_cases j; rfl
  have h0 : opNg (localDataV v) a (0 : Matrix (Fin r) (Fin r) Fv) (Φ : PtG m r Fv → ℂ) = Φ := by
    funext X
    simp [opNg]
  rw [hid, hid, opNg_extC, h1, h0]

lemma isTensG_wEps : IsTensG v a (wEps r : Sp (r + 1) Fv) (spW : Sp 1 Fv) 1 := by
  have h := (((isTensG_nEps (v := v) (a := a) (m := m) (r := r)).mul (isTensG_W (v := v) (a := a)).inv).mul
    isTensG_nEps).mul (isTensG_W (v := v) (a := a)) |>.mul isTensG_nEps
  rw [spN_one_spW] at h
  have e : (1 : Sp r Fv) * (spW : Sp r Fv)⁻¹ * 1 * spW * 1 = 1 := by simp
  rw [e] at h
  exact h

lemma isTensG_embSp_W : IsTensG v a (embSp (spW : Sp r Fv)) 1 spW := by
  have h := (isTensG_wEps (v := v) (a := a) (m := m) (r := r)).inv.mul (isTensG_W (v := v) (a := a))
  have e : (wEps r : Sp (r + 1) Fv)⁻¹ * spW = embSp spW := by
    conv_lhs => rw [spW_eq_wEps_mul (r := r) (k := Fv)]
    rw [inv_mul_cancel_left]
  rw [e, inv_mul_cancel, inv_one, one_mul] at h
  exact h

/-- **$\omega_{r+1}(\iota\delta)(\varphi\otimes\Phi) = \varphi\otimes\omega_r(\delta)\Phi$** for $\delta \in \mathrm{Sp}_{2r}(F_v)$. -/
theorem weilRepSpV_embSp_tensG (δ : Sp r Fv) (φ : Sg (localDataV v) m 1) (Φ : Sg (localDataV v) m r) :
    ((weilRepSpV v a (r + 1) (embSp δ) ⟨tensG φ Φ, tensG_mem φ.2 Φ.2⟩ : Sg (localDataV v) m (r + 1)) :
      PtG m (r + 1) Fv → ℂ) = tensG φ (weilRepSpV v a r δ Φ) := by
  have key : IsTensG v a (embSp δ) 1 δ := by
    have hmem : δ ∈ Submonoid.closure (Set.range (spGen (g := r) (k := Fv))) := by
      rw [spGen_closure]; trivial
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      rcases y with B | A | _
      · exact isTensG_N B.1 B.2
      · exact isTensG_M A
      · exact isTensG_embSp_W
    | one => rw [map_one]; exact IsTensG.one
    | mul x y _ _ hx hy =>
      rw [map_mul]
      simpa using hx.mul hy
  have h := key φ Φ
  rw [map_one, Module.End.one_apply] at h
  exact h

/-- The lattice function factors: $\mathbf 1_{L_v^{r+1}} = \mathbf 1_{L_v}\otimes\mathbf 1_{L_v^r}$. -/
lemma oneSG_succ : oneSG v m (r + 1) = tensS (oneSG v m 1) (oneSG v m r) := by
  refine Subtype.ext ?_
  funext X
  simp [coe_oneSG, tensS, oneG, ptG, tensG, headG, tailG, Fin.prod_univ_succ, Finset.prod_mul_distrib]

/-- **$f_{r+1}(\iota\delta) = f_r(\delta)$ for the lattice sections:**
$(\omega_{r+1}(\iota\delta)\mathbf 1_{L_v^{r+1}})(0) = (\omega_r(\delta)\mathbf 1_{L_v^r})(0)$. -/
theorem secRV_oneSG_embSp (δ : Sp r Fv) :
    secRV v a (oneSG v m (r + 1)) (embSp δ) = secRV v a (oneSG v m r) δ := by
  have hb : QuadFormsKB.Analysis.ballIndV v 0 0 0 = 1 := by
    simp [QuadFormsKB.Analysis.ballIndV]
  have h1 : (oneG v m 1 : PtG m 1 Fv → ℂ) 0 = 1 := by
    simp [oneG, ptG, hb]
  rw [secRV_eq, secRV_eq, oneSG_succ, tensS, weilRepSpV_embSp_tensG]
  simp only [tensG]
  have e1 : headG (0 : PtG m (r + 1) Fv) = 0 := rfl
  have e2 : tailG (0 : PtG m (r + 1) Fv) = 0 := rfl
  rw [e1, e2]
  show (oneG v m 1 : PtG m 1 Fv → ℂ) 0 * _ = _
  rw [h1, one_mul]

end Local

end QuadFormsKB.SiegelWeil.Forms
