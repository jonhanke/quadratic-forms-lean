/-
# O'Meara's Lemma 104:1: representation by a lattice from local representation, up to a square factor

**Layer:** lattices $K$ in $V = F^n$ (`Lat F n`), `Q : QuadForm F n` nondegenerate over a number field $F$, the genus and
the class finiteness theorem `ClassFin.exists_genus_reps` (O'Meara 103:4).

**Proves** `exists_scale_represents` (O'Meara 1973, 104:1, p. 311, in the form used in step 3 of 104:3): given a finite
set $T_1$ of primes at which $O(K_\mathfrak p)$ contains a symmetry, there is $\mu \in F^\times$, a unit at every
$\mathfrak p \in T_1$, such that every $c \in F^\times$ represented by $V$ with $c/\mu^2$ represented by every $K_\mathfrak p$
is represented by $K$.

*Departures from O'Meara.* O'Meara asks $\mu$ to be a unit on a set $T$
chosen in advance and the class representatives $L_i$ to agree with $L$ on $T$ (Example 102:4). Here $\mu$ is a unit only
on $T_1$, and the representatives are moved into agreement with $K$ on $T_1$ by a global isometry obtained from weak
approximation for products of symmetries (`exists_symmProd_approx`); the parity of the word length is fixed with the
given symmetry in $O(K_\mathfrak p)$. The step "$c/\mu^2 \in Q(L_\mathfrak p)$ at good primes" is moved into the hypothesis.
-/
import QuadFormsKB.Lattices.SAWeak
import QuadFormsKB.Lattices.ClassFinite

open NumberField IsDedekindDomain Matrix Topology WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

theorem symmProd_append_replicate {K : Type*} [Field K] [Algebra F K] [CharZero K] (l : List (Fin n → K))
    (x : Fin n → K) (k : ℕ) : symmProd Q K (l ++ List.replicate (2 * k) x) = symmProd Q K l := by
  rw [symmProd_append, symmProd_replicate_two_mul, mul_one]

/-- **Moving a lattice of the genus into agreement with $K$ on $T_1$** by a global isometry (O'Meara 102:4 on $T_1$),
given a symmetry of $K_\mathfrak p$ at each $\mathfrak p \in T_1$. -/
@[kb "omeara1963" "§102A, 102:4, pp. 299–300; cassels1978 Ch. 9, Lemma 4.2, p. 140"]
theorem exists_isometric_agree (hQ : Q.Nondegenerate) (K : Lat F n) (T₁ : Finset (HeightOneSpectrum (𝓞 F)))
    (himp : ∀ v ∈ T₁, ∃ e : Fin n → v.adicCompletion F, Q.evalIn _ e ≠ 0 ∧
      locAct v ((symm Q (v.adicCompletion F) e : orthGroup Q _) : GL (Fin n) _) (loc v K.1) = loc v K.1)
    (M : Lat F n) (hM : SameGenus Q K.1 M.1) :
    ∃ M' : Lat F n, IsIsometric Q M.1 M'.1 ∧ ∀ v ∈ T₁, loc v M'.1 = loc v K.1 := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  have hMo : M ∈ MulAction.orbit (OAf Q) K := by rw [orbit_eq_genus]; exact hM
  obtain ⟨h, hh⟩ := hMo
  have hlocM : ∀ v, loc v M.1 = locAct v ((h v : orthGroup Q _) : GL (Fin n) _) (loc v K.1) := by
    intro v; rw [← hh]; exact loc_latSMul Q h K v
  choose! e he heK using himp
  -- local words of even length for `ε_v h_v⁻¹`
  have hword : ∀ v ∈ T₁, ∃ l : List (Fin n → v.adicCompletion F), Even l.length ∧ (∀ x ∈ l, Q.evalIn _ x ≠ 0) ∧
      locAct v ((symmProd Q _ l : orthGroup Q _) : GL (Fin n) _) (loc v M.1) = loc v K.1 := by
    intro v hv
    obtain ⟨l, hla, hl⟩ := exists_symmProd_eq Q (v.adicCompletion F) hQ (h v)⁻¹
    have hinv : locAct v (((h v)⁻¹ : orthGroup Q _) : GL (Fin n) _) (loc v M.1) = loc v K.1 := by
      rw [hlocM, ← locAct_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, locAct_one]
    rcases Nat.even_or_odd l.length with hev | hodd
    · exact ⟨l, hev, hla, by rw [hl, hinv]⟩
    · refine ⟨e v :: l, by rw [List.length_cons]; exact hodd.add_one, fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact he v hv
        · exact hla x hx
      · rw [symmProd_cons, hl, Subgroup.coe_mul, locAct_mul, hinv, heK v hv]
  choose! l hlev hla hlK using hword
  set N := T₁.sup fun v => (l v).length
  have hNev : Even N := Finset.sup_induction (p := Even) (by simp) (fun a ha b hb => by
      rcases le_total a b with h | h
      · rw [max_eq_right h]; exact hb
      · rw [max_eq_left h]; exact ha) fun v hv => hlev v hv
  set l' : ∀ v : HeightOneSpectrum (𝓞 F), List (Fin n → v.adicCompletion F) :=
    fun v => l v ++ List.replicate (N - (l v).length) (e v)
  have hl' : ∀ v ∈ T₁, (l' v).length = N ∧ (∀ x ∈ l' v, Q.evalIn _ x ≠ 0) ∧
      symmProd Q _ (l' v) = symmProd Q _ (l v) := by
    intro v hv
    have hle : (l v).length ≤ N := Finset.le_sup (f := fun v => (l v).length) hv
    obtain ⟨k, hk⟩ : Even (N - (l v).length) := (Nat.even_sub hle).mpr (by simp [hNev, hlev v hv])
    refine ⟨by simp [l']; omega, fun x hx => ?_, ?_⟩
    · rcases List.mem_append.mp hx with h | h
      · exact hla v hv x h
      · rw [List.eq_of_mem_replicate h]; exact he v hv
    · simp only [l']; rw [show N - (l v).length = 2 * k by omega, symmProd_append_replicate]
  choose U hU hUσ using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_mem_nhds_locAct_eq v ((symmProd Q _ (l v) : orthGroup Q _) : GL (Fin n) _) (loc_isLattice v M.2)
  obtain ⟨ys, -, hys⟩ := exists_symmProd_approx Q T₁ N l' (fun v hv => ⟨(hl' v hv).1, (hl' v hv).2.1⟩) U
    (fun v hv => by rw [(hl' v hv).2.2]; exact hU v)
  set γ := symmProd Q F ys
  refine ⟨Lat.image (γ : GL (Fin n) F) M, ⟨γ, γ.2, rfl⟩, fun v hv => ?_⟩
  rw [Lat.image, loc_glImage]
  have hγv : GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (γ : GL (Fin n) F) =
      ((symmProd Q _ (ys.map (locVec v)) : orthGroup Q _) : GL (Fin n) _) := by
    rw [← orthMap_symmProd]; rfl
  rw [hγv, hUσ v _ (hys v hv), hlK v hv]

theorem locVec_smul' (v : HeightOneSpectrum (𝓞 F)) (μ : F) (x : Fin n → F) :
    locVec v (μ • x) = algebraMap F (v.adicCompletion F) μ • locVec v x := by
  rw [LinearMap.map_smul]; funext i; simp [Algebra.smul_def]

theorem smul_loc_le (v : HeightOneSpectrum (𝓞 F)) {L L' : Submodule (𝓞 F) (Fin n → F)} (a : F)
    (h : ∀ x ∈ L, a • x ∈ L') : ∀ y ∈ loc v L, algebraMap F (v.adicCompletion F) a • y ∈ loc v L' := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    rw [← locVec_smul']; exact locVec_mem_loc v (h x hx)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem smul_mem_of_valued_le {v : HeightOneSpectrum (𝓞 F)} {M : Submodule (v.adicCompletionIntegers F)
    (Fin n → v.adicCompletion F)} {a : v.adicCompletion F} (ha : Valued.v a ≤ 1) {y : Fin n → v.adicCompletion F}
    (hy : y ∈ M) : a • y ∈ M :=
  M.smul_mem (⟨a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ha⟩ : v.adicCompletionIntegers F) hy

/-- **O'Meara 1973, Lemma 104:1** (p. 311), in the form used for 104:3; see the module docstring. -/
@[kb "omeara1963" "§104, 104:1, p. 311"]
theorem exists_scale_represents_away (hQ : Q.Nondegenerate) (K : Lat F n)
    (T₁ : Finset (HeightOneSpectrum (𝓞 F)))
    (himp : ∀ v ∈ T₁, ∃ e : Fin n → v.adicCompletion F, Q.evalIn _ e ≠ 0 ∧
      locAct v ((symm Q (v.adicCompletion F) e : orthGroup Q _) : GL (Fin n) _) (loc v K.1) = loc v K.1) :
    ∃ μ : F, μ ≠ 0 ∧ (∀ v ∈ T₁, Valued.v (algebraMap F (v.adicCompletion F) μ) = 1) ∧
      ∀ E : Finset (HeightOneSpectrum (𝓞 F)), ∀ c : F, c ≠ 0 → Q.RepresentsIn F c →
        (∀ v ∉ E, ∃ y ∈ loc v K.1, Q.evalIn (v.adicCompletion F) y = algebraMap F _ (c / μ ^ 2)) →
        ∃ y : Fin n → F, Q.evalIn F y = c ∧ ∀ v ∉ E, locVec v y ∈ loc v K.1 := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨s, hsg, hs⟩ := ClassFin.exists_genus_reps Q hQ K
  -- representatives agreeing with `K` on `T₁`
  have hadj : ∀ M ∈ s, ∃ M' : Lat F n, IsIsometric Q M.1 M'.1 ∧ ∀ v ∈ T₁, loc v M'.1 = loc v K.1 := by
    intro M hM
    exact exists_isometric_agree Q hQ K T₁ himp M (hsg M hM)
  choose! adj hadjI hadjT using hadj
  -- a common denominator `d` with `d • adj M ⊆ K`
  have hden : ∀ M ∈ s, ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x ∈ (adj M).1, d • x ∈ K.1 := by
    intro M _
    obtain ⟨d₁, hd₁, -, h1⟩ := exists_global_bounds (adj M).2
    obtain ⟨d₂, hd₂, h2, -⟩ := exists_global_bounds K.2
    refine ⟨d₂ * d₁, mul_ne_zero hd₂ hd₁, fun x hx => ?_⟩
    rw [mul_smul]; exact h2 _ (h1 x hx)
  choose! dM hdM0 hdM using hden
  set d : 𝓞 F := ∏ M ∈ s, dM M
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun M hM => hdM0 M hM
  have hdK : ∀ M ∈ s, ∀ x ∈ (adj M).1, d • x ∈ K.1 := by
    intro M hM x hx
    rw [show d = (∏ M' ∈ s.erase M, dM M') * dM M from (Finset.prod_erase_mul _ _ hM).symm, mul_smul]
    exact K.1.smul_mem _ (hdM M hM x hx)
  -- the scalar `μ`
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by simpa using hd0
  set P := (Filter.eventually_cofinite.mp (eventually_not_mem hd0)).toFinset
  have hP : ∀ v, v ∉ P → d ∉ v.asIdeal := by
    intro v hv; by_contra hc; exact hv ((Filter.eventually_cofinite.mp (eventually_not_mem hd0)).mem_toFinset.mpr (not_not.mpr hc))
  have hdv0 : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 F) (v.adicCompletion F) d ≠ 0 := by
    intro v; rw [IsScalarTower.algebraMap_apply (𝓞 F) F]; exact (map_ne_zero _).mpr hdF
  choose kd hkd using fun v : HeightOneSpectrum (𝓞 F) => exists_valued_eq_exp v (hdv0 v)
  obtain ⟨μ', hμ'T, hμ'out⟩ := exists_scalar_approx (T₁ ∪ P) (fun v => if v ∈ T₁ then 1 else 0)
    (fun v => if v ∈ T₁ then {x | Valued.v (x - 1) ≤ exp (-1 : ℤ)} else {x | Valued.v (x - 0) ≤ exp (-(-kd v))})
    (fun v _ => by
      split_ifs
      · exact valued_le_mem_nhds v 1 1
      · exact valued_le_mem_nhds v 0 (-kd v))
  have hμ'unit : ∀ v ∈ T₁, Valued.v (algebraMap F (v.adicCompletion F) μ') = 1 := by
    intro v hv
    have h := hμ'T v (Finset.mem_union_left _ hv)
    simp only [hv, ite_true, Set.mem_ofPred_eq] at h
    have hlt : Valued.v (algebraMap F (v.adicCompletion F) μ' - 1) < Valued.v (1 : v.adicCompletion F) := by
      rw [map_one]; exact h.trans_lt (by rw [← exp_zero, exp_lt_exp]; norm_num)
    rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
  set μ : F := if μ' = 0 then algebraMap (𝓞 F) F d else μ'
  have hμ0 : μ ≠ 0 := by simp only [μ]; split_ifs with h; exacts [hdF, h]
  have hμT : ∀ v ∈ T₁, Valued.v (algebraMap F (v.adicCompletion F) μ) = 1 := by
    intro v hv
    have h1 := hμ'unit v hv
    have hne : μ' ≠ 0 := by rintro rfl; rw [map_zero, map_zero] at h1; exact zero_ne_one h1
    simp only [μ, hne, ite_false]; exact h1
  have hμK : ∀ M ∈ s, ∀ v (y : Fin n → v.adicCompletion F), y ∈ loc v (adj M).1 →
      algebraMap F (v.adicCompletion F) μ • y ∈ loc v K.1 := by
    intro M hM v y hy
    have hdK' := smul_loc_le v (algebraMap (𝓞 F) F d) (fun x hx => by
      rw [algebraMap_smul]; exact hdK M hM x hx) y hy
    by_cases h0 : μ' = 0
    · simp only [μ, h0, ite_true]; exact hdK'
    simp only [μ, h0, ite_false]
    by_cases hv : v ∈ T₁
    · rw [← hadjT M hM v hv]
      exact smul_mem_of_valued_le (hμ'unit v hv).le hy
    · have hd' : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d) ≠ 0 := by
        rw [← IsScalarTower.algebraMap_apply]; exact hdv0 v
      have e : algebraMap F (v.adicCompletion F) μ' • y =
          (algebraMap F (v.adicCompletion F) μ' / algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)) •
            (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d) • y) := by
        rw [smul_smul, div_mul_cancel₀ _ hd']
      rw [e]
      refine smul_mem_of_valued_le ?_ hdK'
      rw [map_div₀, ← IsScalarTower.algebraMap_apply]
      by_cases hvP : v ∈ P
      · have h := hμ'T v (Finset.mem_union_right _ hvP)
        simp only [hv, ite_false, Set.mem_ofPred_eq, sub_zero, neg_neg] at h
        rw [div_le_one₀ (by rw [hkd v]; exact exp_pos), hkd v]; exact h
      · have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d) = 1 := by
          rw [valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff]; exact hP v hvP
        rw [h1, div_one]
        exact hμ'out v (by simp [hv, hvP])
  -- the main argument
  refine ⟨μ, hμ0, hμT, fun E c hc hrep hloc => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hrep
  set x' : Fin n → F := μ⁻¹ • x₀
  have hx' : Q.evalIn F x' = c / μ ^ 2 := by
    simp only [x']; rw [evalIn_smul_sq, hx₀, Algebra.algebraMap_self, RingHom.id_apply]; field_simp
  have hW : ∀ v : HeightOneSpectrum (𝓞 F), ∃ σ : orthGroup Q (v.adicCompletion F),
      (locVec v x' ∈ loc v K.1 ∨ v ∈ E → σ = 1) ∧ (v ∉ E → omat σ *ᵥ locVec v x' ∈ loc v K.1) := by
    intro v
    by_cases hin : locVec v x' ∈ loc v K.1 ∨ v ∈ E
    · refine ⟨1, fun _ => rfl, fun hvE => ?_⟩
      simpa [omat] using hin.resolve_right hvE
    push Not at hin
    obtain ⟨hin, hvE⟩ := hin
    refine ?_
    obtain ⟨y, hyK, hy⟩ := hloc v hvE
    have hu : Q.evalIn (v.adicCompletion F) (locVec v x') = algebraMap F _ (c / μ ^ 2) := by
      rw [evalIn_locVec]; exact congrArg _ hx'
    have hu0 : Q.evalIn (v.adicCompletion F) (locVec v x') ≠ 0 := by
      rw [hu]; exact (map_ne_zero _).mpr (div_ne_zero hc (pow_ne_zero 2 hμ0))
    have hyu : Q.evalIn (v.adicCompletion F) y = Q.evalIn (v.adicCompletion F) (locVec v x') := by rw [hy, hu]
    by_cases h : Q.evalIn (v.adicCompletion F) (y - locVec v x') ≠ 0
    · exact ⟨symm Q _ (y - locVec v x'), fun h' => (h'.elim (absurd · hin) (absurd · hvE)), fun _ => by
        rw [symm_sub_apply Q _ hyu h]; exact hyK⟩
    · have h4 := evalIn_sub_add_evalIn_add Q (v.adicCompletion F) hyu
      have h' : Q.evalIn (v.adicCompletion F) (y + locVec v x') ≠ 0 := by
        intro h0
        rw [not_not.mp h, h0, add_zero, hyu] at h4
        have : (4 : v.adicCompletion F) ≠ 0 := by norm_num
        exact hu0 ((mul_eq_zero.mp h4.symm).resolve_left this)
      exact ⟨symm Q _ (y + locVec v x'), fun h' => (h'.elim (absurd · hin) (absurd · hvE)), fun _ => by
        rw [symm_add_apply Q _ hyu h']; exact Submodule.neg_mem _ hyK⟩
  choose σ hσ1 hσK using hW
  have hxstd : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, locVec v x' ∈ std v := by
    have := Filter.eventually_all.mpr fun i : Fin n => eventually_valuation_le_one (F := F) (x' i)
    filter_upwards [this] with v hv i
    rw [locVec_apply', valued_algebraMap, neg_zero, exp_zero]; exact hv i
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, σ v ∈ stdStab Q v := by
    filter_upwards [hxstd, loc_eventually_std K.2] with v h1 h2
    rw [hσ1 v (Or.inl (by rw [h2]; exact h1))]; exact (stdStab Q v).one_mem
  set hA : OAf Q := ⟨σ, hev⟩
  set Nl := latSMul Q hA⁻¹ K
  have hxN : ∀ v ∉ E, locVec v x' ∈ loc v Nl.1 := by
    intro v hvE
    rw [loc_latSMul]
    refine ⟨omat (σ v) *ᵥ locVec v x', hσK v hvE, ?_⟩
    change omat (hA⁻¹ v) *ᵥ (omat (σ v) *ᵥ locVec v x') = locVec v x'
    rw [mulVec_mulVec, ← omat_mul]
    have : hA⁻¹ v = (σ v)⁻¹ := rfl
    rw [this, inv_mul_cancel, omat_one, one_mulVec]
  have hNg : SameGenus Q K.1 Nl.1 := by
    have : Nl ∈ MulAction.orbit (OAf Q) K := ⟨hA⁻¹, rfl⟩
    rw [orbit_eq_genus] at this; exact this
  obtain ⟨M, hMs, hNM⟩ := hs Nl hNg
  obtain ⟨γ, hγ, hγN⟩ := hNM.trans Q (hadjI M hMs)
  have hγx : ∀ v ∉ E, locVec v ((γ : Matrix (Fin n) (Fin n) F) *ᵥ x') ∈ loc v (adj M).1 := by
    intro v hvE
    rw [← hγN, loc_glImage, locVec_mulVec]
    exact ⟨locVec v x', hxN v hvE, rfl⟩
  refine ⟨μ • ((γ : Matrix (Fin n) (Fin n) F) *ᵥ x'), ?_, fun v hvE => ?_⟩
  · rw [evalIn_smul_sq, evalIn_mulVec_of_mem Q hγ, hx']
    field_simp
  · rw [locVec_smul']; exact hμK M hMs v _ (hγx v hvE)

/-- **O'Meara 1973, Lemma 104:1** (p. 311), in the form used for 104:3; see the module docstring. -/
@[kb "omeara1963" "§104, 104:1, p. 311"]
theorem exists_scale_represents (hQ : Q.Nondegenerate) (K : Lat F n) (T₁ : Finset (HeightOneSpectrum (𝓞 F)))
    (himp : ∀ v ∈ T₁, ∃ e : Fin n → v.adicCompletion F, Q.evalIn _ e ≠ 0 ∧
      locAct v ((symm Q (v.adicCompletion F) e : orthGroup Q _) : GL (Fin n) _) (loc v K.1) = loc v K.1) :
    ∃ μ : F, μ ≠ 0 ∧ (∀ v ∈ T₁, Valued.v (algebraMap F (v.adicCompletion F) μ) = 1) ∧
      ∀ c : F, c ≠ 0 → Q.RepresentsIn F c →
        (∀ v, ∃ y ∈ loc v K.1, Q.evalIn (v.adicCompletion F) y = algebraMap F _ (c / μ ^ 2)) →
        ∃ y ∈ K.1, Q.evalIn F y = c := by
  obtain ⟨μ, hμ0, hμT, h⟩ := exists_scale_represents_away Q hQ K T₁ himp
  refine ⟨μ, hμ0, hμT, fun c hc hrep hloc => ?_⟩
  obtain ⟨y, hy, hyK⟩ := h ∅ c hc hrep (fun v _ => hloc v)
  exact ⟨y, (mem_iff_forall_loc K.2 y).mpr fun v => hyK v (Finset.notMem_empty v), hy⟩

end QuadFormsKB.Lattices
