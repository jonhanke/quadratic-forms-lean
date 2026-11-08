/-
# O'Meara 102:9 under the idèle condition $J_F = P_DJ_F^S$, and the global part of 104:9

**Layer:** $V = F^n$ over a number field $F$ with the form `Q : QuadForm F n`, lattices `Lat F n`, $S$ = all finite
spots; $J_F$ = `IdeleGroup (𝓞 F) F`, $J_F^S$ = `OMeara.sIdeles Set.univ` (`Sec64.lean`), $D = \theta(O^+(V))$ =
`spinorNormGroup Q hQ` (`Sec101B.lean`), $P_D$ = the principal idèles $(\alpha)$, $\alpha \in D$
(`IdeleGroup.unitEmbedding`); the local stabilizer $O(L_\mathfrak p)$ = `locStabV Q v L`, the spinor kernel
$O'(V_\mathfrak p)$ = `spinorKernel`, the proper spinor genus `SameProperSpinorGenus` (`Sec102.lean`).

**Defines** `SpinorNormsContainUnits Q v L`: O'Meara's local hypothesis $\theta(O^+(L_\mathfrak p)) \supseteq
\mathfrak u_\mathfrak p$ (every unit $u$ of $\mathfrak o_\mathfrak p$ is, modulo squares, the spinor norm of a rotation
of $L_\mathfrak p$).

**Proves** (O'Meara 1973)
* `spinorNormsContainUnits_iff`: the hypothesis in terms of `localSpinorNormGroup` ($\theta(O^+(L_\mathfrak p))$,
  `Sec101D.lean`);
* `exists_spinorKernel_mul_of_spinorNormsContainUnits`: under it, every rotation $\sigma \in O^+(V_\mathfrak p)$ whose
  spinor norm is a unit class is $\sigma = \kappa g$ with $\kappa \in O'(V_\mathfrak p)$, $g \in O^+(L_\mathfrak p)$;
* **`omeara102_9`** (102:9, p. 304): if $J_F = P_DJ_F^S$ and $\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$
  for every finite $\mathfrak p$, then $\operatorname{spn}^+L = \operatorname{gen}L$. No dimension hypothesis
  (as in the book). Unconditional.
* **`omeara104_9_of_local`** (104:9, p. 320, global part): if moreover $n \ge 3$ and $V$ is indefinite, then
  $\operatorname{cls}^+L = \operatorname{gen}L$ (with 104:5, `isProperIsometric_of_sameProperSpinorGenus`, strong
  approximation, unconditional in the library). Unconditional.

*Proof of 102:9 (O'Meara's).* For $K = hL$ in $\operatorname{gen}L$ take $h \in J_V$ with rotations at every spot
(`exists_oaf_soSub`). Let $S_0$ be the finite set of $\mathfrak p$ with $h_\mathfrak p \notin O(L_\mathfrak p)$ and $i$ the
idèle with $i_\mathfrak p = x_\mathfrak p$, a representative of $\theta(h_\mathfrak p)$, for $\mathfrak p \in S_0$, and
$1$ elsewhere. Write $i = (\alpha)j$ with $\alpha \in D$, $j \in J_F^S$, and take $\gamma \in O^+(V)$ with
$\theta(\gamma) = \alpha$. Then $\theta(\gamma_\mathfrak p^{-1}h_\mathfrak p) = \alpha x_\mathfrak p \equiv j_\mathfrak p$ is a
unit class for $\mathfrak p \in S_0$, while for $\mathfrak p \notin S_0$, $h_\mathfrak p \in O(L_\mathfrak p)$ and
$\theta(\gamma_\mathfrak p) = \alpha$ is a unit class ($1 = \alpha j_\mathfrak p$). The local hypothesis gives
$\gamma^{-1}h \in J'_V\,O(\hat L)$, i.e. $K = \gamma\Sigma L$ with $\Sigma \in J'_V$.

*Deviation.* $S$ is the set of all finite spots (as in `OMeara104_9`).
-/
import QuadFormsKB.Literature.OMeara.Sec102To104
import QuadFormsKB.Literature.Cassels.Ch11Sec3
import QuadFormsKB.Literature.Cassels.Ch11Sec1Indef

open NumberField IsDedekindDomain Matrix
open QuadFormsKB.OMeara (ideleAt ideleAt_mul ideleAt_one ideleAt_ofAdic_self ideleAt_ofAdic_ne)

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-! ### The local hypothesis $\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$ -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **$\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$** (O'Meara 1973, §102B, hypothesis of 102:9, p. 304),
at the finite spot $\mathfrak p$ = `v` for the lattice $L$: for every $u \in F_\mathfrak p$ with $\lvert u\rvert_\mathfrak p = 1$
(`Valued.v u = 1`, a unit of $\mathfrak o_\mathfrak p$) there is a rotation $g \in O^+(L_\mathfrak p)$, i.e.
$g \in O(L_\mathfrak p)$ (`locStabV Q v L`) with $\det g = 1$ (`detHom`), whose spinor norm is
$\theta(g) = u\,F_\mathfrak p^{\times 2}$ (`sqClassOf u`). Equivalently every unit lies in `localSpinorNormGroup`
(`spinorNormsContainUnits_iff`). -/
@[kb "omeara1963" "§102B, 102:9, p. 304 (hypothesis θ(O⁺(L_𝔭)) ⊇ 𝔲_𝔭)"]
def SpinorNormsContainUnits (L : Lat F n) : Prop :=
  ∀ u : Fv, Valued.v u = 1 → ∃ g ∈ locStabV Q v L, detHom Q Fv g = 1 ∧ spinorNorm Q Fv g = sqClassOf u

/-- **The hypothesis of 102:9 through $\theta(O^+(L_\mathfrak p))$** (O'Meara 1973, §102B, p. 304, with §101D,
p. 297): `SpinorNormsContainUnits Q v L` holds if and only if every unit $u \in \mathfrak o_\mathfrak p^\times$ lies in
$\theta(O^+(L_\mathfrak p))$ = `localSpinorNormGroup Q hQ v L`. -/
@[kb "omeara1963" "§102B, 102:9, p. 304 (θ(O⁺(L_𝔭)) ⊇ 𝔲_𝔭, via §101D)"]
theorem spinorNormsContainUnits_iff (hQ : Q.Nondegenerate) (L : Lat F n) :
    SpinorNormsContainUnits Q v L ↔
      ∀ u : Fvˣ, Valued.v (u : Fv) = 1 → u ∈ localSpinorNormGroup Q hQ v L := by
  constructor
  · intro h u hu
    obtain ⟨g, hg, hd, hθ⟩ := h u hu
    refine (mem_localSpinorNormGroup Q hQ v L).mpr ⟨g, ⟨hg, ?_⟩, ?_⟩
    · change g ∈ Tamagawa.soSub Q Fv
      rw [Tamagawa.mem_soSub, ← detHom_val, hd, Units.val_one]
    · rw [hθ, sqClassOf_of_ne_zero u.ne_zero, Units.mk0_val]
  · intro h u hu
    have hu0 : u ≠ 0 := by rintro rfl; rw [map_zero] at hu; exact zero_ne_one hu
    obtain ⟨g, hg, hθ⟩ := (mem_localSpinorNormGroup Q hQ v L).mp (h (Units.mk0 u hu0) hu)
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    refine ⟨g, hg1, Units.ext ?_, ?_⟩
    · rw [detHom_val, Units.val_one]; exact hg2
    · rw [hθ, sqClassOf_of_ne_zero hu0]

/-- **Rotations with unit spinor norm under $\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$** (O'Meara 1973,
§102B, proof of 102:9, p. 304): if `SpinorNormsContainUnits Q v L`, then every rotation $\sigma \in O^+(V_\mathfrak p)$
whose spinor norm is a unit class (`IsUnitSqClass`) is $\sigma = \kappa g$ with $\kappa \in O'(V_\mathfrak p)$
(`spinorKernel`) and $g \in O(L_\mathfrak p)$ with $\det g = 1$. -/
@[kb "omeara1963" "§102B, 102:9, p. 304 (proof: O⁺(V_𝔭) ∩ θ⁻¹(𝔲_𝔭) = O'(V_𝔭)O⁺(L_𝔭))"]
theorem exists_spinorKernel_mul_of_spinorNormsContainUnits (hQ : Q.Nondegenerate) (L : Lat F n)
    (hL : SpinorNormsContainUnits Q v L) {σ : orthGroup Q Fv} (hσ : σ ∈ Tamagawa.soSub Q Fv)
    (hc : IsUnitSqClass v (spinorNorm Q Fv σ)) :
    ∃ k ∈ spinorKernel Q Fv, ∃ g ∈ locStabV Q v L, detHom Q Fv g = 1 ∧ σ = k * g := by
  obtain ⟨k, hk, hkσ⟩ := exists_spinorKernel_mul_locStab_of_rot hQ v L
    ((spinorNormsContainUnits_iff Q v hQ L).mp hL) hσ hc
  refine ⟨k, hk, k⁻¹ * σ, hkσ, ?_, by group⟩
  have hk1 : detHom Q Fv k = 1 := by
    rw [spinorKernel_eq_ker Q Fv hQ] at hk
    exact (Subgroup.mem_inf.mp hk).2
  have hσ1 : detHom Q Fv σ = 1 := Units.ext (by rw [detHom_val, Units.val_one]; exact hσ)
  rw [map_mul, map_inv, hk1, hσ1]; simp

end Local

/-! ### 102:9: $\operatorname{spn}^+L = \operatorname{gen}L$ -/

section Global

/-- **O'Meara 102:9** (O'Meara 1973, §102B, Theorem 102:9, p. 304), for $S$ = all finite spots of the number field
$F$: let $L$ be a lattice on the regular space $V = (F^n, Q)$ (`hQ`). Suppose $J_F = P_DJ_F^S$ (`hJ`: every idèle
$i \in J_F$ is $i = (\alpha)\,j$ with $\alpha \in D = \theta(O^+(V))$ (`spinorNormGroup Q hQ`) and $j \in J_F^S$
(`OMeara.sIdeles Set.univ`, a unit at every finite spot), exactly as in `OMeara104_9`). If
$\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$ for all $\mathfrak p$ (`SpinorNormsContainUnits`), then
$\operatorname{spn}^+L = \operatorname{gen}L$: every $K$ with `SameGenus Q L K` is in the proper spinor genus of $L$
(`SameProperSpinorGenus Q L K`). No dimension hypothesis. Unconditional. -/
@[kb "omeara1963" "§102B, 102:9, p. 304"]
theorem omeara102_9 (hQ : Q.Nondegenerate)
    (hJ : ∀ i : IdeleGroup (𝓞 F) F, ∃ α ∈ spinorNormGroup Q hQ,
      ∃ j ∈ OMeara.sIdeles (Set.univ : Set (HeightOneSpectrum (𝓞 F))),
        i = IdeleGroup.unitEmbedding (𝓞 F) F α * j)
    (L : Lat F n) (hloc : ∀ v, SpinorNormsContainUnits Q v L) {K : Lat F n} (hK : SameGenus Q L.1 K.1) :
    SameProperSpinorGenus Q L K := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨h, hrot, hhK⟩ := exists_oaf_soSub hQ L hK
  subst hhK
  -- local spinor norms `θ(h_v) = x_v`
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : v.adicCompletion F, x ≠ 0 ∧
      spinorNorm Q (v.adicCompletion F) (h v) = sqClassOf x := by
    intro v
    obtain ⟨xs, hxs, hxe⟩ := exists_symmProd_eq Q (v.adicCompletion F) hQ (h v)
    exact ⟨_, valProd_ne_zero Q _ hxs, by rw [← hxe, spinorNorm_symmProd Q _ hQ xs hxs]⟩
  choose xv hxv0 hxvθ using hx
  -- the finite set `S₀` of spots where `h_v ∉ O(L_v)`
  have hfin : {v | h v ∉ locStabV Q v L}.Finite := by
    refine ((Filter.eventually_cofinite.mp h.2).union
      (Filter.eventually_cofinite.mp (loc_eventually_std L.2))).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hv ((locStabV_eq_stdStab Q v L hc.2).mpr hc.1)
  set S := hfin.toFinset
  -- the idèle `i` with `i_v = x_v` on `S₀` and `1` elsewhere
  let i : IdeleGroup (𝓞 F) F :=
    ∏ v ∈ S, IdeleGroup.ofAdicCompletion (𝓞 F) F v (Units.mk0 (xv v) (hxv0 v))
  have hiv : ∀ v, ideleAt i v = if v ∈ S then xv v else 1 := by
    intro v
    let φ : IdeleGroup (𝓞 F) F →* v.adicCompletion F :=
      { toFun := fun x => ideleAt x v, map_one' := ideleAt_one v, map_mul' := fun x y => ideleAt_mul x y v }
    change φ i = _
    simp only [i, map_prod]
    split_ifs with hv
    · rw [Finset.prod_eq_single_of_mem v hv]
      · exact ideleAt_ofAdic_self v _
      · intro v' _ hv'
        exact ideleAt_ofAdic_ne v' v (Ne.symm hv') _
    · refine Finset.prod_eq_one fun v' hv' => ?_
      exact ideleAt_ofAdic_ne v' v (fun e => hv (e ▸ hv')) _
  -- the idèle condition: `i = (α) j`
  obtain ⟨α, hαD, j, hj, hij⟩ := hJ i
  have hiαj : ∀ v, ideleAt i v = algebraMap F (v.adicCompletion F) (α : F) * ideleAt j v := by
    intro v; rw [hij]; rfl
  have hjv : ∀ v, Valued.v (ideleAt j v) = 1 := fun v => hj v (Set.mem_univ v)
  have hj0 : ∀ v, ideleAt j v ≠ 0 := fun v e => by
    have := hjv v; rw [e, map_zero] at this; exact zero_ne_one this
  have ha0 : (α : F) ≠ 0 := α.ne_zero
  obtain ⟨γ, hγ, hγθ⟩ := (mem_spinorNormGroup Q hQ).mp hαD
  have hγθ' : spinorNorm Q F γ = sqClassOf (α : F) := by
    rw [hγθ, sqClassOf_of_ne_zero ha0, Units.mk0_val]
  have hθγ : ∀ v : HeightOneSpectrum (𝓞 F), spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ) =
      sqClassOf (algebraMap F (v.adicCompletion F) (α : F)) := fun v => spinorNorm_orthMap_of hQ v γ ha0 hγθ'
  have hγrot : ∀ v : HeightOneSpectrum (𝓞 F), orthMap Q (v.adicCompletion F) γ ∈
      Tamagawa.soSub Q (v.adicCompletion F) := by
    intro v
    rw [Tamagawa.mem_soSub, orthMap_val, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      show ((γ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 from hγ, map_one]
  -- local decomposition `γ_v⁻¹ h_v = k_v u_v`
  have hdec : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k ∈ spinorKernel Q (v.adicCompletion F),
      k⁻¹ * ((orthMap Q _ γ)⁻¹ * h v) ∈ locStabV Q v L := by
    intro v
    set Kv := v.adicCompletion F
    have hloc' := (spinorNormsContainUnits_iff Q v hQ L).mp (hloc v)
    set a := algebraMap F Kv (α : F)
    have hav : a ≠ 0 := (map_ne_zero _).mpr ha0
    by_cases hvS : v ∈ S
    · refine exists_spinorKernel_mul_locStab_of_rot hQ v L hloc'
        ((Tamagawa.soSub Q Kv).mul_mem ((Tamagawa.soSub Q Kv).inv_mem (hγrot v)) (hrot v)) ?_
      rw [← spinorNormHom_apply Q Kv hQ, map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hθγ,
        SqClass.inv_eq, hxvθ, ← sqClassOf_mul hav (hxv0 v)]
      have hx : xv v = a * ideleAt j v := by rw [← hiαj, hiv, if_pos hvS]
      refine ⟨ideleAt j v, hjv v, ?_⟩
      rw [hx, ← mul_assoc, sqClassOf_mul (mul_ne_zero hav hav) (hj0 v),
        (sqClassOf_eq_one_iff (mul_ne_zero hav hav)).mpr ⟨a, rfl⟩, one_mul]
    · have hhv : h v ∈ locStabV Q v L := by
        by_contra hc; exact hvS (hfin.mem_toFinset.mpr hc)
      have h1 : a * ideleAt j v = 1 := by rw [← hiαj, hiv, if_neg hvS]
      have hva : Valued.v a = 1 := by
        have := congrArg Valued.v h1
        rw [map_mul, hjv v, mul_one, map_one] at this
        exact this
      obtain ⟨k, hk, hg⟩ := exists_spinorKernel_mul_locStab_of_rot hQ v L hloc' (hγrot v) (by
        rw [hθγ]; exact ⟨_, hva, rfl⟩)
      set g := k⁻¹ * orthMap Q Kv γ
      refine ⟨g⁻¹ * k⁻¹ * g, ?_, ?_⟩
      · have := (spinorKernel_normal Q Kv).conj_mem k⁻¹ ((spinorKernel Q Kv).inv_mem hk) g⁻¹
        simpa using this
      · have e : (g⁻¹ * k⁻¹ * g)⁻¹ * ((orthMap Q Kv γ)⁻¹ * h v) = g⁻¹ * h v := by
          simp only [g]; group
        rw [e]
        exact (locStabV Q v L).mul_mem ((locStabV Q v L).inv_mem hg) hhv
  choose kv hkv hukv using hdec
  -- the adelic element `u ∈ O(L̂)`
  let uA : OAf Q := ⟨fun v => (kv v)⁻¹ * ((orthMap Q _ γ)⁻¹ * h v), by
    filter_upwards [loc_eventually_std L.2] with v hv
    exact (locStabV_eq_stdStab Q v L hv).mp (hukv v)⟩
  have huA : uA ∈ locStab Q L := fun v => hukv v
  set k : OAf Q := (diagF Q γ)⁻¹ * h * uA⁻¹ with hkdef
  have hk : k ∈ spinorKernelAf Q := by
    intro v
    have : k v = kv v := by
      change (orthMap Q _ γ)⁻¹ * h v * ((kv v)⁻¹ * ((orthMap Q _ γ)⁻¹ * h v))⁻¹ = kv v
      group
    rw [this]; exact hkv v
  have hh : h = diagF Q γ * k * uA := by simp only [k]; group
  refine (sameProperSpinorGenus_iff Q).mpr ⟨γ, hγ, k, hk, ?_⟩
  have huL : latSMul Q uA L = L :=
    MulAction.mem_stabilizer_iff.mp ((stabilizer_eq_locStab Q L).symm ▸ huA)
  change h • L = (diagF Q γ) • (k • L)
  conv_lhs => rw [hh, mul_smul, mul_smul]
  change diagF Q γ • (k • latSMul Q uA L) = _
  rw [huL]

/-- **O'Meara 104:9, from the local condition** (O'Meara 1973, §104, Theorem 104:9, p. 320, with the local
hypothesis of 102:9 in place of "$L$ modular or maximal"), for $S$ = all finite spots of the number field $F$: let
$V = (F^n, Q)$ be regular (`hQ`) with $n \ge 3$, $S$ indefinite for $V$ (`IsIndefinite Q`: $V_w$ isotropic at some
infinite spot $w$), and $J_F = P_DJ_F^S$ (`hJ`, as in `OMeara104_9`). If $\theta(O^+(L_\mathfrak p)) \supseteq
\mathfrak u_\mathfrak p$ for every finite $\mathfrak p$ (`SpinorNormsContainUnits`), then $\operatorname{cls}^+L =
\operatorname{gen}L$: every $K$ in $\operatorname{gen}L$ is properly isometric to $L$. *Proof:* 102:9 (`omeara102_9`)
and 104:5 (`isProperIsometric_of_sameProperSpinorGenus`). The step from "modular or maximal" to the local condition
(Example 102:10 / 92:5, 93:20, 91:9) is not part of this theorem. Unconditional. -/
@[kb "omeara1963" "§104, 104:9, p. 320 (from the local condition θ(O⁺(L_𝔭)) ⊇ 𝔲_𝔭)"]
theorem omeara104_9_of_local (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (hind : IsIndefinite Q)
    (hJ : ∀ i : IdeleGroup (𝓞 F) F, ∃ α ∈ spinorNormGroup Q hQ,
      ∃ j ∈ OMeara.sIdeles (Set.univ : Set (HeightOneSpectrum (𝓞 F))),
        i = IdeleGroup.unitEmbedding (𝓞 F) F α * j)
    (L : Lat F n) (hloc : ∀ v, SpinorNormsContainUnits Q v L) {K : Lat F n} (hK : SameGenus Q L.1 K.1) :
    IsProperIsometric Q L.1 K.1 :=
  isProperIsometric_of_sameProperSpinorGenus Q hn hQ hind (omeara102_9 Q hQ hJ L hloc hK)

end Global

end QuadFormsKB.Lattices

