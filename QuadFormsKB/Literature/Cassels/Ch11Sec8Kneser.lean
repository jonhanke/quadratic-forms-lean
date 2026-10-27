/-
# Cassels, Chapter 11, §8: Kneser's theorem on equivalence away from one prime (Theorem 8.4)

**Layer:** $V = \mathbb Q^n$ with the form $Q$ = `Q : QuadForm ℚ n`; lattices `Lat ℚ n`, localizations, local
isometries `orthGroup Q ℚ_p` acting by `locAct`; $\theta(\Lambda_p)$ = `localSpinorNormGroup`; strong approximation
away from a prime at which $V$ is isotropic (`strongApproximationSpinAt`, Cassels' Theorem 8.2); $\theta(V) \supseteq
\mathbb Q_+$ (Lemma 3.2, `mem_spinorNormGroup_rat_iff`).

**Proves** Cassels' Theorem 8.4 (Kneser 1957, p. 233) in the language of lattices
(`exists_soSub_locAct_eq_of_local_rat`): let $n \ge 3$ and $V$ isotropic over $\mathbb Q_q$; if $\Lambda_p$ and
$\Gamma_p$ are isometric for every prime $p \ne q$ and $U_p \subseteq \theta(\Lambda_p)$ for every $p \ne q$, then there
is $\sigma \in O^+(V)$ with $\sigma\Lambda_p = \Gamma_p$ for all $p \ne q$: the $\mathbb Z[1/q]$-lattices
$\Lambda[1/q]$ and $\Gamma[1/q]$ are properly equivalent. Cassels states it for $q = 2$, forms of the same determinant
$d$ with $p^{n(n-1)/2} \nmid d$ for $p \ne 2$; that condition gives $U_p \subseteq \theta(\Lambda_p)$ by Lemma 3.7,
Corollary (`valued_det_le_of_not_units_mem`). *Proof* (Cassels: "left with confidence to the reader (cf. Lemma 3.6,
Corollary)"): write $\Gamma_p = \beta_p\Lambda_p$ with rotations $\beta_p$ ($\beta_q = 1$); choose $c > 0$ with
$c\,\theta(\beta_p)$ a unit class for $p \ne q$ and $\gamma \in O^+(V)$ with $\theta(\gamma) = c$ (Lemma 3.2); then
$\gamma^{-1}\beta_p = \delta_p\rho_p$ with $\delta_p$ in the spinor kernel and $\rho_p \in O^+(\Lambda_p)$ for $p \ne q$;
strong approximation away from $q$ gives $\alpha$ in the spinor kernel of $O(V)$ with $\alpha^{-1}\delta_p \in
O(\Lambda_p)$ for $p \ne q$; take $\sigma = \gamma\alpha$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3
import QuadFormsKB.Lattices.SATernaryAway

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- Kneser's theorem over a number field with `𝓞 F` a PID, given that the positive-type global spinor norms
realize every `a₀` up to a unit (`hval`). -/
theorem exists_soSub_locAct_eq_of_local_units {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)]
    {n : ℕ} (Q : QuadForm F n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (hval : ∀ a₀ : 𝓞 F, a₀ ≠ 0 → ∃ u : (𝓞 F)ˣ, ∃ a ∈ spinorNormGroup Q hQ,
      (a : F) = algebraMap (𝓞 F) F ((u : 𝓞 F) * a₀))
    (q : HeightOneSpectrum (𝓞 F)) (hq : Q.IsotropicIn (q.adicCompletion F)) (L M : Lat F n)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), v ≠ q →
      ∃ g ∈ orthGroup Q (v.adicCompletion F), locAct v g (loc v L.1) = loc v M.1)
    (hunits : ∀ v : HeightOneSpectrum (𝓞 F), v ≠ q → ∀ u : (v.adicCompletion F)ˣ,
      Valued.v (u : v.adicCompletion F) = 1 → u ∈ localSpinorNormGroup Q hQ v L) :
    ∃ σ ∈ Tamagawa.soSub Q F, ∀ v : HeightOneSpectrum (𝓞 F), v ≠ q →
      locAct v ((orthMap Q (v.adicCompletion F) σ : orthGroup Q _) : GL (Fin n) _) (loc v L.1) = loc v M.1 := by
  classical
  have hn0 : 0 < n := by omega
  -- rotations carrying `L_v` to `M_v` for `v ≠ q`
  have hpg : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : orthGroup Q (v.adicCompletion F), v ≠ q →
      (g ∈ Tamagawa.soSub Q (v.adicCompletion F) ∧ locAct v (g : GL (Fin n) _) (loc v L.1) = loc v M.1) := by
    intro v
    by_cases hv : v = q
    · exact ⟨1, fun h => absurd hv h⟩
    obtain ⟨g, hg, he⟩ := hloc v hv
    rcases Tamagawa.det_eq_one_or_neg_one Q hQ ⟨g, hg⟩ with h1 | h1
    · exact ⟨⟨g, hg⟩, fun _ => ⟨h1, he⟩⟩
    · obtain ⟨τ, hτ, hτL⟩ := exists_det_neg_one_locAct_eq Q v hQ hn0 (loc_isLattice v L.2)
      refine ⟨⟨g, hg⟩ * τ, fun _ => ⟨?_, ?_⟩⟩
      · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul]
        change g.val.det * _ = 1
        rw [show g.val.det = -1 from h1, hτ]; ring
      · rw [Subgroup.coe_mul, locAct_mul, hτL]; exact he
  choose k0 hk0 using hpg
  let hp : (v : HeightOneSpectrum (𝓞 F)) → orthGroup Q (v.adicCompletion F) := fun v =>
    if v = q ∨ loc v L.1 = loc v M.1 then 1 else k0 v
  have hpspec : ∀ v, v ≠ q → locAct v ((hp v : orthGroup Q _) : GL (Fin n) _) (loc v L.1) = loc v M.1 := by
    intro v hv
    simp only [hp]
    split_ifs with he
    · rcases he with he | he
      · exact absurd he hv
      · rw [← he]; exact locAct_one _
    · exact (hk0 v hv).2
  have hprot : ∀ v, hp v ∈ Tamagawa.soSub Q (v.adicCompletion F) := by
    intro v
    simp only [hp]
    split_ifs with he
    · exact (Tamagawa.soSub Q _).one_mem
    · exact (hk0 v (fun h => he (Or.inl h))).1
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, hp v ∈ stdStab Q v := by
    filter_upwards [loc_eventually_std L.2, loc_eventually_std M.2] with v h1 h2
    have : loc v L.1 = loc v M.1 := h1.trans h2.symm
    simp only [hp, this, or_true, ↓reduceIte]
    exact (stdStab Q v).one_mem
  let h : OAf Q := ⟨hp, hev⟩
  have hhq : h q = 1 := by simp [h, hp]
  have hpspec' : ∀ v, v ≠ q → locAct v ((h v : orthGroup Q _) : GL (Fin n) _) (loc v L.1) = loc v M.1 := hpspec
  -- local spinor norms `θ(h_v) = x_v`
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : v.adicCompletion F, x ≠ 0 ∧
      spinorNorm Q (v.adicCompletion F) (h v) = sqClassOf x := by
    intro v
    obtain ⟨xs, hxs, hxe⟩ := exists_symmProd_eq Q (v.adicCompletion F) hQ (h v)
    exact ⟨_, valProd_ne_zero Q _ hxs, by rw [← hxe, spinorNorm_symmProd Q _ hQ xs hxs]⟩
  choose xv hxv0 hxvθ using hx
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v => WithZero.log (Valued.v (xv v))
  let ε : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (m v % 2).toNat
  have hm : ∀ v, Valued.v (xv v) = WithZero.exp (m v) := fun v =>
    (WithZero.exp_log ((map_ne_zero _).mpr (hxv0 v))).symm
  have hε : ∀ v, ((ε v : ℕ) : ℤ) = m v % 2 := fun v => Int.toNat_of_nonneg (Int.emod_nonneg _ two_ne_zero)
  have hfin : {v | h v ∉ locStabV Q v L}.Finite := by
    refine ((Filter.eventually_cofinite.mp h.2).union
      (Filter.eventually_cofinite.mp (loc_eventually_std L.2))).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hv ((locStabV_eq_stdStab Q v L hc.2).mpr hc.1)
  set S := hfin.toFinset
  set a₀ : 𝓞 F := ∏ w ∈ S, primeGen w ^ ε w with ha₀def
  have ha₀ : a₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (primeGen_ne_zero w)
  obtain ⟨u, a, haD, hau⟩ := hval a₀ ha₀
  have hvalue : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) (a : F)) =
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a₀) := by
    intro v
    rw [hau, ← IsScalarTower.algebraMap_apply, map_mul, map_mul, valued_unit v u, one_mul]
  have hva : ∀ v ∈ S, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = WithZero.exp (-(ε v : ℤ)) := by
    intro v hv
    rw [hvalue]
    exact valued_prod_primeGen_of_mem v ε hv
  have hva' : ∀ v ∉ S, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 := by
    intro v hv
    rw [hvalue]
    exact valued_prod_primeGen_of_not_mem v ε hv
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  obtain ⟨γ, hγ, hγθ⟩ := (mem_spinorNormGroup Q hQ).mp haD
  have hγθ' : spinorNorm Q F γ = sqClassOf (a : F) := by
    rw [hγθ, sqClassOf_of_ne_zero ha0]; exact congrArg (SqClass.mk (K := F)) (Units.ext rfl)
  have hθγ : ∀ v : HeightOneSpectrum (𝓞 F), spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ) =
      sqClassOf (algebraMap F (v.adicCompletion F) (a : F)) := fun v => spinorNorm_orthMap_of hQ v γ ha0 hγθ'
  have hγrot : ∀ v : HeightOneSpectrum (𝓞 F), orthMap Q (v.adicCompletion F) γ ∈
      Tamagawa.soSub Q (v.adicCompletion F) := by
    intro v
    rw [Tamagawa.mem_soSub, orthMap_val, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      show ((γ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 from hγ, map_one]
  have hdec : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k ∈ spinorKernel Q (v.adicCompletion F),
      v ≠ q → k⁻¹ * ((orthMap Q _ γ)⁻¹ * h v) ∈ locStabV Q v L := by
    intro v
    by_cases hvq : v = q
    · exact ⟨1, (spinorKernel Q _).one_mem, fun h => absurd hvq h⟩
    set K := v.adicCompletion F
    have hav : algebraMap F K (a : F) ≠ 0 := (map_ne_zero _).mpr ha0
    by_cases hvS : v ∈ S
    · obtain ⟨k, hk, hg⟩ := exists_spinorKernel_mul_locStab_of_rot hQ v L (hunits v hvq)
        ((Tamagawa.soSub Q K).mul_mem ((Tamagawa.soSub Q K).inv_mem (hγrot v)) (hprot v)) (by
        rw [← spinorNormHom_apply Q K hQ, map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hθγ,
          SqClass.inv_eq, (show spinorNorm Q K (hp v) = sqClassOf (xv v) from hxvθ v), ← sqClassOf_mul hav (hxv0 v)]
        refine isUnitSqClass_of_valued_eq v _ (m v / 2) ?_
        rw [map_mul, hva v hvS, hm, ← WithZero.exp_add, hε]
        congr 1
        omega)
      exact ⟨k, hk, fun _ => hg⟩
    · have hhv : h v ∈ locStabV Q v L := by
        by_contra hc; exact hvS (hfin.mem_toFinset.mpr hc)
      obtain ⟨k, hk, hg⟩ := exists_spinorKernel_mul_locStab_of_rot hQ v L (hunits v hvq) (hγrot v) (by
        rw [hθγ]; exact ⟨_, hva' v hvS, rfl⟩)
      set g := k⁻¹ * orthMap Q K γ
      refine ⟨g⁻¹ * k⁻¹ * g, ?_, fun _ => ?_⟩
      · have := (spinorKernel_normal Q K).conj_mem k⁻¹ ((spinorKernel Q K).inv_mem hk) g⁻¹
        simpa using this
      · have e : (g⁻¹ * k⁻¹ * g)⁻¹ * ((orthMap Q K γ)⁻¹ * h v) = g⁻¹ * h v := by
          simp only [g]; group
        rw [e]
        exact (locStabV Q v L).mul_mem ((locStabV Q v L).inv_mem hg) hhv
  choose kv hkv hukv using hdec
  let uA : OAf Q := ⟨fun v => (kv v)⁻¹ * ((orthMap Q _ γ)⁻¹ * h v), by
    filter_upwards [loc_eventually_std L.2, Filter.eventually_cofinite_ne q] with v hv hvq
    exact (locStabV_eq_stdStab Q v L hv).mp (hukv v hvq)⟩
  set k : OAf Q := (diagF Q γ)⁻¹ * h * uA⁻¹ with hkdef
  have hkv' : ∀ v, k v = kv v := by
    intro v
    change (orthMap Q _ γ)⁻¹ * h v * ((kv v)⁻¹ * ((orthMap Q _ γ)⁻¹ * h v))⁻¹ = kv v
    group
  have hk : k ∈ spinorKernelAf Q := by
    intro v
    rw [hkv']; exact hkv v
  obtain ⟨α, hα, hαL⟩ := strongApproximationSpinAt.approx Q hn hQ q hq L k hk
  refine ⟨γ * α, (Tamagawa.soSub Q F).mul_mem hγ (spinorKernel_le_soSub Q F hα), fun w hw => ?_⟩
  have hkw : locAct w (((k w : orthGroup Q _)) : GL (Fin n) _) (loc w L.1) =
      locAct w ((orthMap Q (w.adicCompletion F) α : orthGroup Q _) : GL (Fin n) _) (loc w L.1) := by
    have e := hαL w hw
    have hsplit : (((diagF Q α)⁻¹ * k) w : orthGroup Q _) = (orthMap Q _ α)⁻¹ * k w := rfl
    rw [hsplit, Subgroup.coe_mul, locAct_mul, Subgroup.coe_inv] at e
    have e' := congrArg (locAct w ((orthMap Q (w.adicCompletion F) α : orthGroup Q _) : GL (Fin n) _)) e
    rwa [← locAct_mul, mul_inv_cancel, locAct_one] at e'
  have hρ : locAct w ((((kv w)⁻¹ * ((orthMap Q _ γ)⁻¹ * h w) : orthGroup Q _)) : GL (Fin n) _) (loc w L.1)
      = loc w L.1 := hukv w hw
  have e : (h w : orthGroup Q _) = (orthMap Q (w.adicCompletion F) γ * kv w) *
      ((kv w)⁻¹ * ((orthMap Q _ γ)⁻¹ * h w)) := by group
  have hhL : locAct w ((h w : orthGroup Q _) : GL (Fin n) _) (loc w L.1) =
      locAct w ((orthMap Q (w.adicCompletion F) γ * kv w : orthGroup Q _) : GL (Fin n) _) (loc w L.1) := by
    conv_lhs => rw [e, Subgroup.coe_mul, locAct_mul, hρ]
  rw [← hpspec' w hw, hhL, map_mul, Subgroup.coe_mul, locAct_mul, ← hkw, hkv' w, Subgroup.coe_mul, locAct_mul]

/-- **Cassels, Theorem 8.4** (Ch. 11, p. 233; Kneser 1957), lattice form: *let $f_1, f_2$ be two classically integral
forms of the same determinant $d$ in $n \ge 3$ variables, both isotropic over $\mathbb Q_2$, equivalent over $\mathbb R$
and over $\mathbb Z_p$ for all $p \ne 2$, with $p^{n(n-1)/2} \nmid d$ for all $p \ne 2$. Then $f_1, f_2$ are properly
equivalent over $\mathbb Z^{(2)}$.* Here for lattices $L, M$ on one regular space $V$ of dimension $n \ge 3$ isotropic
at a prime $q$ (Cassels: $q = 2$): if $L_p \cong M_p$ and $U_p \subseteq \theta(L_p)$ for every prime $p \ne q$, then
$\sigma L_p = M_p$ for all $p \ne q$ with one $\sigma \in O^+(V)$. -/
@[kb "cassels1978" "Ch. 11, Thm. 8.4, p. 233 (lattice form; any prime q in place of 2; U_p ⊆ θ(Λ_p) for p ≠ q)"]
theorem exists_soSub_locAct_eq_of_local_rat {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (q : HeightOneSpectrum (𝓞 ℚ)) (hq : Q.IsotropicIn (q.adicCompletion ℚ)) (L M : Lat ℚ n)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ q →
      ∃ g ∈ orthGroup Q (v.adicCompletion ℚ), locAct v g (loc v L.1) = loc v M.1)
    (hunits : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ q → ∀ u : (v.adicCompletion ℚ)ˣ,
      Valued.v (u : v.adicCompletion ℚ) = 1 → u ∈ localSpinorNormGroup Q hQ v L) :
    ∃ σ ∈ Tamagawa.soSub Q ℚ, ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ q →
      locAct v ((orthMap Q (v.adicCompletion ℚ) σ : orthGroup Q _) : GL (Fin n) _) (loc v L.1) = loc v M.1 := by
  classical
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective
  have key := exists_soSub_locAct_eq_of_local_units (F := ℚ) Q hQ hn
  have hval : ∀ a₀ : 𝓞 ℚ, a₀ ≠ 0 → ∃ u : (𝓞 ℚ)ˣ, ∃ a ∈ spinorNormGroup Q hQ,
      (a : ℚ) = algebraMap (𝓞 ℚ) ℚ ((u : 𝓞 ℚ) * a₀) := by
    intro a₀ ha₀
    have hq : (algebraMap (𝓞 ℚ) ℚ a₀) ≠ 0 := by
      intro h
      exact ha₀ ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 ℚ) ℚ)).mp h)
    by_cases hpos : 0 < algebraMap (𝓞 ℚ) ℚ a₀
    · refine ⟨1, Units.mk0 (algebraMap (𝓞 ℚ) ℚ a₀) hq, ?_, by simp⟩
      exact (mem_spinorNormGroup_rat_iff Q hQ hn _).mpr (Or.inr hpos)
    · have hneg : 0 < -(algebraMap (𝓞 ℚ) ℚ a₀) := by
        rcases lt_or_gt_of_ne hq with h | h
        · linarith
        · exact absurd h hpos
      refine ⟨-1, Units.mk0 (-(algebraMap (𝓞 ℚ) ℚ a₀)) (neg_ne_zero.mpr hq), ?_, by simp⟩
      exact (mem_spinorNormGroup_rat_iff Q hQ hn _).mpr (Or.inr hneg)
  have hq' : @QuadForm.IsotropicIn ℚ Rat.instField.toCommRing n (HeightOneSpectrum.adicCompletion ℚ q)
      (HeightOneSpectrum.adicCompletion.instField ℚ q).toCommRing
      (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ q) Q := by
    convert hq; exact Subsingleton.elim _ _
  obtain ⟨σ, hσ, hσv⟩ := key hval q hq' L M (fun v hv => by
    obtain ⟨g, hg, he⟩ := hloc v hv
    exact ⟨g, by convert hg; exact Subsingleton.elim _ _, he⟩) hunits
  refine ⟨σ, hσ, fun v hv => ?_⟩
  have := hσv v hv
  convert this <;> exact Subsingleton.elim _ _

end QuadFormsKB.Lattices
