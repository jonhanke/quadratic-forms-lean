/-
# O'Meara Example 102:5: local representations and the genus

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n`; lattices `Lat F n`, their
localizations `loc 𝔭 L`, local isometries `orthGroup Q F_𝔭` acting by `locAct`, and the gluing of local lattices
(`LocFamily.glue`, O'Meara 81:14).

**Proves** Example 102:5 (O'Meara 1973, §102A, p. 300):
* `exists_sameGenus_le`: if $K$ is a finitely generated $\mathcal O_F$-submodule of $V$ and at each spot $\mathfrak p$
  some $\varphi_\mathfrak p \in O(V_\mathfrak p)$ has $\varphi_\mathfrak pL_\mathfrak p \supseteq K_\mathfrak p$, then
  $K \subseteq L'$ for some $L' \in \operatorname{gen}L$;
* `exists_sameGenus_represents`: the special case of a scalar: if $\alpha \ne 0$ is represented by $V$ and by
  $L_\mathfrak p$ at every spot, then $\alpha$ is represented by some $L' \in \operatorname{gen}L$.

*Deviation.* O'Meara's hypothesis is a representation $K_\mathfrak p \to L_\mathfrak p$ at each spot, which by Witt's
theorem extends to an isometry $\varphi_\mathfrak p^{-1}$ of $V_\mathfrak p$; the library has Witt's theorem only for one
vector (`Lattices.ClassFin.exists_orth_mulVec_eq`, here `exists_orth_mulVec_eq_local` over $F_\mathfrak p$), so the
general statement takes the extended isometries $\varphi_\mathfrak p$ as its hypothesis, and the scalar case (one
vector) is derived in full. Only the finite spots occur (as in `SameGenus`).
-/
import QuadFormsKB.Lattices.ClassFinite

open NumberField IsDedekindDomain Matrix Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Moving a vector by a local isometry** (Witt's theorem for one vector, O'Meara 42:17, over $F_\mathfrak p$): if
$Q(x) = Q(y) \ne 0$ then $\gamma x = y$ for some $\gamma \in O(V_\mathfrak p)$. Same proof as
`ClassFin.exists_orth_mulVec_eq`. -/
theorem exists_orth_mulVec_eq_local (v : HeightOneSpectrum (𝓞 F)) {x y : Fin n → v.adicCompletion F}
    (hxy : Q.evalIn _ x = Q.evalIn _ y) (hx : Q.evalIn _ x ≠ 0) :
    ∃ γ ∈ orthGroup Q (v.adicCompletion F), γ.val *ᵥ x = y := by
  have hyx : Q.evalIn (v.adicCompletion F) y = Q.evalIn (v.adicCompletion F) x := hxy.symm
  by_cases h1 : Q.evalIn (v.adicCompletion F) (y - x) ≠ 0
  · exact ⟨_, (symm Q (v.adicCompletion F) (y - x)).2, symm_sub_apply Q (v.adicCompletion F) hyx h1⟩
  · have h4 := evalIn_sub_add_evalIn_add Q (v.adicCompletion F) hyx
    have hy : Q.evalIn (v.adicCompletion F) y ≠ 0 := hyx ▸ hx
    have h2 : Q.evalIn (v.adicCompletion F) (y + x) ≠ 0 := by
      intro h0; rw [not_not.mp h1, h0, add_zero] at h4
      exact hy (by linear_combination -h4 / 4)
    refine ⟨(symm Q (v.adicCompletion F) y : GL (Fin n) (v.adicCompletion F)) *
      (symm Q (v.adicCompletion F) (y + x) : GL (Fin n) (v.adicCompletion F)),
      (orthGroup Q (v.adicCompletion F)).mul_mem (symm Q _ y).2 (symm Q _ (y + x)).2, ?_⟩
    rw [Units.val_mul, ← mulVec_mulVec, symm_add_apply Q _ hyx h2, symm_neg_self Q _ hy]

/-- A finitely generated $K$ has bounded denominators: $eK \subseteq \mathcal O_F^n$ for some $e \ne 0$. -/
theorem exists_smul_le_intVec {K : Submodule (𝓞 F) (Fin n → F)} (hK : K.FG) :
    ∃ e : 𝓞 F, e ≠ 0 ∧ ∀ x ∈ K, e • x ∈ intVec := by
  classical
  obtain ⟨s, rfl⟩ := hK
  choose c hc0 hc using fun x : Fin n → F => exists_smul_mem_intVec x
  refine ⟨∏ x ∈ s, c x, Finset.prod_ne_zero_iff.mpr fun x _ => hc0 x, fun y hy => ?_⟩
  let S : Submodule (𝓞 F) (Fin n → F) := intVec.comap ((∏ x ∈ s, c x) • LinearMap.id)
  have hle : Submodule.span (𝓞 F) (s : Set (Fin n → F)) ≤ S := by
    rw [Submodule.span_le]
    intro x hx
    simp only [S, SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← Finset.mul_prod_erase s c hx, mul_comm, mul_smul]
    exact intVec.smul_mem _ (hc x)
  have := hle hy
  simpa [S] using this

/-- **Example 102:5** (O'Meara 1973, §102A, p. 300): let $L$ be a lattice on $V$ and $K$ a finitely generated
$\mathcal O_F$-submodule of $V$ such that at each spot $\mathfrak p$ some isometry $\varphi_\mathfrak p \in O(V_\mathfrak p)$
has $K_\mathfrak p \subseteq \varphi_\mathfrak pL_\mathfrak p$ (by Witt's theorem, this is the case when $K_\mathfrak p$ is
represented by $L_\mathfrak p$). Then $K \subseteq L'$ for some lattice $L'$ in the genus of $L$; O'Meara's $L'$ is
$\varphi_\mathfrak pL_\mathfrak p$ at the finitely many spots where $K_\mathfrak p \not\subseteq L_\mathfrak p$ and
$L_\mathfrak p$ elsewhere. -/
@[kb "omeara1963" "§102A, 102:5, p. 300 (variant: the local representations given as isometries of V_𝔭)"]
theorem exists_sameGenus_le (L : Lat F n) {K : Submodule (𝓞 F) (Fin n → F)} (hK : K.FG)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g ∈ orthGroup Q (v.adicCompletion F),
      loc v K ≤ locAct v g (loc v L.1)) :
    ∃ L' : Lat F n, SameGenus Q L.1 L'.1 ∧ K ≤ L'.1 := by
  classical
  choose g hg hgK using h
  obtain ⟨e, he0, he⟩ := exists_smul_le_intVec hK
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, loc v K ≤ loc v L.1 := by
    filter_upwards [eventually_not_mem he0, loc_eventually_std L.2] with v hv hL
    have hk : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) e) = WithZero.exp (-(0 : ℤ)) := by
      rw [valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff.mpr hv]; simp
    rw [hL]
    simpa using loc_le_ball v he hk
  let M : LocFamily F n :=
    { M := fun v => if loc v K ≤ loc v L.1 then loc v L.1 else locAct v (g v) (loc v L.1)
      isLattice := fun v => by
        split_ifs
        · exact loc_isLattice v L.2
        · exact locAct_isLattice _ (loc_isLattice v L.2)
      eventually_std := by
        filter_upwards [hev, loc_eventually_std L.2] with v hv hL
        simp only [hv, ↓reduceIte]; exact hL }
  refine ⟨⟨M.glue, M.glue_isLattice⟩, fun v => ?_, ?_⟩
  · change ∃ g ∈ orthGroup Q _, locAct v g (loc v L.1) = loc v M.glue
    rw [M.loc_glue]
    change ∃ g' ∈ orthGroup Q _, locAct v g' (loc v L.1) =
      if loc v K ≤ loc v L.1 then loc v L.1 else locAct v (g v) (loc v L.1)
    split_ifs
    · exact ⟨1, (orthGroup Q _).one_mem, locAct_one _⟩
    · exact ⟨g v, hg v, rfl⟩
  · rw [le_iff_forall_loc M.glue_isLattice]
    intro v
    rw [M.loc_glue]
    change loc v K ≤ if loc v K ≤ loc v L.1 then loc v L.1 else locAct v (g v) (loc v L.1)
    split_ifs with hv
    · exact hv
    · exact hgK v

/-- **Example 102:5, the case of a scalar** (O'Meara 1973, §102A, p. 300): if a scalar $\alpha \ne 0$ is represented
by $V$ and by $L_\mathfrak p$ at every spot $\mathfrak p$, then $\alpha$ is represented by some lattice $L'$ in the genus
of $L$. -/
@[kb "omeara1963" "§102A, 102:5, p. 300 (the special case of a scalar)"]
theorem exists_sameGenus_represents (L : Lat F n) {α : F} (hα : α ≠ 0) {x : Fin n → F}
    (hx : Q.evalIn F x = α)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ y ∈ loc v L.1,
      Q.evalIn (v.adicCompletion F) y = algebraMap F (v.adicCompletion F) α) :
    ∃ L' : Lat F n, SameGenus Q L.1 L'.1 ∧ ∃ z ∈ L'.1, Q.evalIn F z = α := by
  obtain ⟨L', hL', hxL'⟩ := exists_sameGenus_le Q L (K := Submodule.span (𝓞 F) {x})
    (Submodule.fg_span_singleton x) fun v => by
      obtain ⟨y, hy, hyα⟩ := hloc v
      have hxv : Q.evalIn (v.adicCompletion F) (locVec v x) = algebraMap F _ α := by
        rw [evalIn_locVec]; exact congrArg _ hx
      obtain ⟨γ, hγ, hγy⟩ := exists_orth_mulVec_eq_local Q v (x := y) (y := locVec v x)
        (hyα.trans hxv.symm) (by rw [hyα]; exact (map_ne_zero _).mpr hα)
      refine ⟨γ, hγ, ?_⟩
      rw [loc, Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [locVec_smul_int]
      exact Submodule.smul_mem _ _ (hγy ▸ ⟨y, hy, rfl⟩)
  exact ⟨L', hL', x, hxL' (Submodule.mem_span_singleton_self x), hx⟩

end QuadFormsKB.Lattices
