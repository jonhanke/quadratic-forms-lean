import QuadFormsKB.Tamagawa.BinaryCMGenus

/-!
# Classes in the genus of the maximal order of $F(\sqrt{-D})$

**Layer:** as in `BinaryCMGenus.lean`.

**Proves**
* `isLattice_latI`: $c^{-1}(t\mathfrak A)$ is a lattice ($t \ne 0$, $\mathfrak A \ne 0$ an ideal of $\mathcal O_E$).
* **`exists_normOne_smul_iff`** (E-language): for normalized pairs $(\mathfrak A, a)$, $(\mathfrak B, b)$ and scalars $s, t$ with
  $N(s)a = N(t)b = 1$, the lattices $s\mathfrak A$ and $t\mathfrak B$ differ by a norm-one multiplier iff the pairs are properly
  equivalent (`PairRel`).
* **`sameGenus_latI_jPair`**: for $\mathfrak B\mathfrak B' = (\delta)$ the lattice $(\sigma\delta)^{-1}\mathfrak B\,\sigma\mathfrak B' =
  \mathfrak B\,\sigma(\mathfrak B)^{-1}$ lies in the genus of $\mathcal O_E$: at each $\mathfrak p$ it agrees with $u\,\mathcal O_E$, $u = \beta/\sigma\beta$,
  for a local generator $\beta$ of $\mathfrak B$ (`exists_local_gen`, from Mathlib's `IsDedekindDomain.exists_sup_span_eq`).
* **`exists_pair_of_genus`**: every lattice $M$ in the genus of $\mathcal O_E$ is $c^{-1}(d^{-1}\mathfrak A)$ with $N_{E/F}\mathfrak A = (d^2)$
  (`exists_mem_eval_not_mem` and Mathlib's $N\mathfrak A = (N(x) : x \in \mathfrak A)$, `Ideal.relNorm_apply`).

Source: O'Meara 1963, §§81–82, 102 [unverified]; Shimura 2010, §4 [unverified].

-/

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryCM

open Lattices QuadForm QuadFormsKB.HilbertModular Binary.Rel BinaryNormOne

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-! ### Scaling lattices in $E$ -/

theorem smulLat_smulLat (a b : E) (L : Submodule (𝓞 F) E) :
    smulLat a (smulLat b L) = smulLat (a * b) L := by
  ext z
  simp only [mem_smulLat]
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩; exact ⟨w, hw, by ring⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨b * w, ⟨w, hw, rfl⟩, by ring⟩

theorem smulLat_one' (L : Submodule (𝓞 F) E) : smulLat 1 L = L := by
  ext z; simp [mem_smulLat]

theorem smulLat_inv_smulLat {a : E} (ha : a ≠ 0) (L : Submodule (𝓞 F) E) :
    smulLat a⁻¹ (smulLat a L) = L := by
  rw [smulLat_smulLat, inv_mul_cancel₀ ha, smulLat_one']

theorem smulLat_cancel {a : E} (ha : a ≠ 0) {L L' : Submodule (𝓞 F) E} (h : smulLat a L = smulLat a L') :
    L = L' := by
  rw [← smulLat_inv_smulLat ha L, h, smulLat_inv_smulLat ha]

theorem coe_algebraMap_intNorm (x : 𝓞 E) :
    algebraMap F E ((Algebra.intNorm (𝓞 F) (𝓞 E) x : 𝓞 F) : F) = (x : E) * conj F E (x : E) := by
  rw [coe_intNorm, nrm, algebraMap_norm]

theorem algebraMap_intNorm_O (x : 𝓞 E) :
    ((algebraMap (𝓞 F) (𝓞 E) (Algebra.intNorm (𝓞 F) (𝓞 E) x) : 𝓞 E) : E) = (x : E) * conj F E (x : E) := by
  rw [algebraMap_intNorm_eq]
  show algebraMap (𝓞 E) E (x * conjO F E x) = _
  rw [map_mul, algebraMap_conjO]

theorem norm_algebraMap_F (c : F) : Algebra.norm F (algebraMap F E c) = c ^ 2 := by
  rw [Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two]

variable {D : 𝓞 F} (S : SqrtData D E)

local notation "QD" => formF (diagForm1 D)

/-- **The lattice of $t\mathfrak A$** in coordinates, $c^{-1}(t\mathfrak A)$. -/
def latI (t : E) (𝔄 : Ideal (𝓞 E)) : Submodule (𝓞 F) (Fin 2 → F) := latOf S (smulLat t (idealLat F 𝔄))

theorem mem_latI {t : E} {𝔄 : Ideal (𝓞 E)} {x : Fin 2 → F} :
    x ∈ latI S t 𝔄 ↔ ∃ a ∈ 𝔄, t * algebraMap (𝓞 E) E a = cE S x := by
  rw [latI, mem_latOf, mem_smulLat]
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨a, ha, rfl⟩ := mem_idealLat.mp hy
    exact ⟨a, ha, hyx⟩
  · rintro ⟨a, ha, hax⟩
    exact ⟨_, algebraMap_mem_idealLat ha, hax⟩

theorem cE_smul_int (c : 𝓞 F) (x : Fin 2 → F) :
    cE S (c • x) = algebraMap F E (algebraMap (𝓞 F) F c) * cE S x := by
  rw [← algebraMap_smul F c x, cE_smul]

theorem cE_mem_O {x : Fin 2 → F} (hx : x ∈ latE S) : ∃ ω : 𝓞 E, (ω : E) = cE S x :=
  ⟨⟨cE S x, (mem_latE S).mp hx⟩, rfl⟩

/-- **$c^{-1}(t\mathfrak A)$ is a lattice** for $t \ne 0$ and $\mathfrak A \ne 0$: writing $t = x/y$ and choosing $0 \ne a \in \mathfrak A$,
$N(a)N(x)\,\mathcal O_E \subseteq t\mathfrak A$ and $N(y)\,t\mathfrak A \subseteq \mathcal O_E$. -/
theorem isLattice_latI {t : E} (ht : t ≠ 0) {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) : (latI S t 𝔄).IsLattice F := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) t
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at ht
  have hy' : (y : E) ≠ 0 := algebraMap_ne_zero hy0
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔄
  set nA := Algebra.intNorm (𝓞 F) (𝓞 E) a
  set nX := Algebra.intNorm (𝓞 F) (𝓞 E) x
  set nY := Algebra.intNorm (𝓞 F) (𝓞 E) y
  have hnA : nA ≠ 0 := by simpa [nA] using ha0
  have hnX : nX ≠ 0 := by simpa [nX] using hx0
  have hnY : nY ≠ 0 := by simpa [nY] using hy0
  have h1 : ∀ z ∈ intVec, (nA * nX) • z ∈ latI S (algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E y) 𝔄 := by
    intro z hz
    obtain ⟨ω, hω⟩ := cE_mem_O S (intVec_le_latE S hz)
    rw [mem_latI]
    refine ⟨algebraMap (𝓞 F) (𝓞 E) nA * y * conjO F E x * ω, ?_, ?_⟩
    · rw [algebraMap_intNorm_eq, mul_assoc a, mul_assoc a, mul_assoc a]
      exact 𝔄.mul_mem_right _ ha
    · rw [cE_smul_int, map_mul, map_mul, map_mul, map_mul, map_mul, algebraMap_conjO, ← hω]
      rw [show algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) nA) = algebraMap F E (algebraMap (𝓞 F) F nA) from
        algebraMap_O_E nA, coe_algebraMap_intNorm x]
      show (x : E) / (y : E) * (algebraMap F E (nA : F) * (y : E) * conj F E (x : E) * (ω : E)) =
        algebraMap F E (nA : F) * ((x : E) * conj F E (x : E)) * (ω : E)
      field_simp
  have h2 : ∀ m ∈ latI S (algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E y) 𝔄, ((2 * D) * nY) • m ∈ intVec := by
    intro m hm
    obtain ⟨w, -, hw⟩ := (mem_latI S).mp hm
    rw [mul_smul]
    refine smul_mem_intVec_of_mem_latE S ?_
    rw [mem_latE, cE_smul_int, ← hw]
    rw [show algebraMap F E (algebraMap (𝓞 F) F nY) * ((x : E) / (y : E) * (w : E)) =
        (x : E) * conj F E (y : E) * (w : E) by
      rw [show algebraMap F E (algebraMap (𝓞 F) F nY) = (y : E) * conj F E (y : E) from coe_algebraMap_intNorm y]
      field_simp]
    exact (x.2.mul (y.2.map (conj F E))).mul w.2
  refine isLattice_of_global_bounds (d := (nA * nX) * ((2 * D) * nY))
    (mul_ne_zero (mul_ne_zero hnA hnX) (mul_ne_zero (two_mul_ne_zero S) hnY)) ?_ ?_
  · intro z hz
    rw [mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (h1 z hz)
  · intro m hm
    rw [mul_smul]
    exact Submodule.smul_mem _ _ (h2 m hm)

/-! ### Norm-one multipliers and proper equivalence of pairs -/

/-- **Norm-one multipliers between normalized lattices = proper equivalence of pairs.** For ideals $\mathfrak A, \mathfrak B \ne 0$ and
$a, b \in \mathcal O_F$, $s, t \in E$ with $N(s)\,a = N(t)\,b = 1$: some $u$ with $N(u) = 1$ has $u\,s\mathfrak A = t\mathfrak B$ iff
$\alpha\mathfrak A = \beta\mathfrak B$, $N(\beta)\,b = N(\alpha)\,a$ for some nonzero $\alpha, \beta \in \mathcal O_E$ (`PairRel`). -/
theorem exists_normOne_smul_iff {𝔄 𝔅 : Ideal (𝓞 E)} {a b : 𝓞 F} {s t : E}
    (hs : Algebra.norm F s * (a : F) = 1) (ht : Algebra.norm F t * (b : F) = 1) :
    (∃ u : E, Algebra.norm F u = 1 ∧ smulLat u (smulLat s (idealLat F 𝔄)) = smulLat t (idealLat F 𝔅)) ↔
      ∃ α β : 𝓞 E, α ≠ 0 ∧ β ≠ 0 ∧ Ideal.span {α} * 𝔄 = Ideal.span {β} * 𝔅 ∧
        nrm (F := F) β * (b : F) = nrm (F := F) α * (a : F) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hNs : Algebra.norm F s ≠ 0 := Algebra.norm_ne_zero_iff.mpr hs0
  have hNt : Algebra.norm F t ≠ 0 := Algebra.norm_ne_zero_iff.mpr ht0
  constructor
  · rintro ⟨u, hu, h⟩
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    rw [smulLat_smulLat] at h
    have h' : smulLat (u * s / t) (idealLat F 𝔄) = idealLat F 𝔅 := by
      rw [div_eq_mul_inv, mul_comm, ← smulLat_smulLat, h, smulLat_inv_smulLat ht0]
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (u * s / t)
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div, eq_comm] at hxy
      exact div_ne_zero (mul_ne_zero hu0 hs0) ht0 hxy
    refine ⟨x, y, hx0, hy0, (smulLat_idealLat_iff hy0 𝔄 𝔅).mp (by rw [hxy, h']), ?_⟩
    have hN := congrArg (Algebra.norm F) hxy
    rw [norm_div', norm_div', map_mul, hu, one_mul] at hN
    have hny : nrm (F := F) y ≠ 0 := nrm_ne_zero hy0
    simp only [nrm]
    field_simp at hN
    linear_combination (-(Algebra.norm F (algebraMap (𝓞 E) E y) * (b : F))) * hs + (-((a : F) * (b : F))) * hN +
      (Algebra.norm F (algebraMap (𝓞 E) E x) * (a : F)) * ht
  · rintro ⟨α, β, hα, hβ, h1, h2⟩
    have hβ' : (β : E) ≠ 0 := algebraMap_ne_zero hβ
    refine ⟨t * (α : E) / (s * (β : E)), ?_, ?_⟩
    · rw [norm_div', map_mul, map_mul]
      have hnb : Algebra.norm F (β : E) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ'
      rw [div_eq_one_iff_eq (mul_ne_zero hNs hnb)]
      simp only [nrm] at h2
      linear_combination (-(Algebra.norm F t * Algebra.norm F (α : E))) * hs +
        (-(Algebra.norm F s * Algebra.norm F t)) * h2 + (Algebra.norm F s * Algebra.norm F (β : E)) * ht
    · rw [smulLat_smulLat, show t * (α : E) / (s * (β : E)) * s = t * ((α : E) / (β : E)) by
        field_simp, ← smulLat_smulLat, ← (smulLat_idealLat_iff hβ 𝔄 𝔅).mpr h1]

/-! ### Local generators and the genus of $\mathfrak B\,\sigma(\mathfrak B)^{-1}$ -/

/-- **A local generator** of a nonzero ideal $\mathfrak B$ at a prime $\mathfrak p$ of $F$: some $\beta \in \mathfrak B$ and $d \in \mathcal O_F\setminus\mathfrak p$
with $d\,\mathfrak B \subseteq (\beta)$. (Mathlib's `IsDedekindDomain.exists_sup_span_eq` gives $\mathfrak B = \mathfrak B\mathfrak p\mathcal O_E + (\beta)$; then
$(\beta) = \mathfrak B\mathfrak K$ with $\mathfrak K$ prime to $\mathfrak p$, and $d \in N(\mathfrak K)\setminus\mathfrak p$.) -/
theorem exists_local_gen {B : Ideal (𝓞 E)} (hB : B ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ β ∈ B, ∃ d : 𝓞 F, d ∉ v.asIdeal ∧ ∀ b ∈ B, algebraMap (𝓞 F) (𝓞 E) d * b ∈ Ideal.span {β} := by
  set P := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))
  have hP : P ≠ ⊥ := map_ne_bot v.ne_bot
  have hB0 : B ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  have hI : B * P ≠ 0 := mul_ne_zero hB0 (by rwa [Ne, Ideal.zero_eq_bot])
  obtain ⟨β, hβ⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_left (I := B) (J := P)) hI
  have hβB : β ∈ B := hβ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self β)
  obtain ⟨K, hK⟩ : B ∣ Ideal.span {β} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hβB)
  have hKv : ¬ v.asIdeal ∣ Ideal.relNorm (𝓞 F) K := by
    intro hdvd
    obtain ⟨Q, hQ⟩ := exists_dvd_of_dvd_relNorm v K hdvd
    have hle1 : Ideal.span {β} ≤ B * Q.1 := by rw [hK]; exact Ideal.mul_mono_right (Ideal.le_of_dvd hQ)
    have hle2 : B * P ≤ B * Q.1 := Ideal.mul_mono_right (map_le_primesOver Q)
    have hle : B ≤ B * Q.1 := by conv_lhs => rw [← hβ]
                                 exact sup_le hle2 hle1
    obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
    have h1 : (1 : Ideal (𝓞 E)) = Q.1 * C := by
      apply mul_left_cancel₀ hB0
      rw [mul_one, ← mul_assoc]; exact hC
    apply primesOver_ne_top Q
    rw [eq_top_iff, ← Ideal.one_eq_top, h1]
    exact Ideal.mul_le_left
  obtain ⟨d, hd, hdv⟩ : ∃ d ∈ Ideal.relNorm (𝓞 F) K, d ∉ v.asIdeal := by
    by_contra h
    push Not at h
    exact hKv (Ideal.dvd_iff_le.mpr h)
  refine ⟨β, hβB, d, hdv, fun b hb => ?_⟩
  have hdK : algebraMap (𝓞 F) (𝓞 E) d ∈ K := by
    have : algebraMap (𝓞 F) (𝓞 E) d ∈ K * conjIdeal F K := by
      rw [mul_conjIdeal]; exact Ideal.mem_map_of_mem _ hd
    exact Ideal.mul_le_left this
  rw [hK, mul_comm]
  exact Ideal.mul_mem_mul hdK hb

/-- If $d \notin \mathfrak p$ and $dL \subseteq L'$ then $L_\mathfrak p \subseteq L'_\mathfrak p$. -/
theorem loc_le_of_smul_mem (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} {L L' : Submodule (𝓞 F) (Fin n → F)} {d : 𝓞 F}
    (hd : d ∉ v.asIdeal) (h : ∀ x ∈ L, d • x ∈ L') : loc v L ≤ loc v L' := by
  rw [loc, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have hv : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d) = 1 := by
    rw [valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff.mpr hd]
  have hd0 : algebraMap (𝓞 F) (v.adicCompletion F) d ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hc : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹ ≤ 1 := by rw [map_inv₀, hv, inv_one]
  have e : locVec v x = toO v _ hc • locVec v (d • x) := by
    rw [locVec_smul_int, smul_smul]
    have : toO v _ hc * algebraMap (𝓞 F) (v.adicCompletionIntegers F) d = 1 := by
      apply Subtype.ext
      show (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹ * algebraMap (𝓞 F) (v.adicCompletion F) d = 1
      exact inv_mul_cancel₀ hd0
    rw [this, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (locVec_mem_loc v (h x hx))

theorem conjO_algebraMap (d : 𝓞 F) : conjO F E (algebraMap (𝓞 F) (𝓞 E) d) = algebraMap (𝓞 F) (𝓞 E) d := by
  apply FaithfulSMul.algebraMap_injective (𝓞 E) E
  rw [algebraMap_conjO, algebraMap_O_E, AlgEquiv.commutes]

/-- **$\mathfrak B\,\sigma(\mathfrak B)^{-1} = (\sigma\delta)^{-1}\mathfrak B\,\sigma\mathfrak B'$ lies in the genus of $\mathcal O_E$** ($\mathfrak B\mathfrak B' = (\delta)$): at each
$\mathfrak p$, with a local generator $\beta$ of $\mathfrak B$ and $u = \beta/\sigma\beta$ ($N(u) = 1$), $d\cdot(\sigma\delta)^{-1}\mathfrak B\sigma\mathfrak B' \subseteq
u\mathcal O_E$ and $d\cdot u\mathcal O_E \subseteq (\sigma\delta)^{-1}\mathfrak B\sigma\mathfrak B'$ with $d \notin \mathfrak p$, so the localizations agree with
$\gamma_u(\mathcal O_E)_\mathfrak p$. -/
theorem sameGenus_latI_jPair {B B' : Ideal (𝓞 E)} (hB : B ≠ ⊥) {δ : 𝓞 E} (hδ : δ ≠ 0)
    (h : B * B' = Ideal.span {δ}) :
    SameGenus QD (latE S) (latI S (conj F E (δ : E))⁻¹ (B * conjIdeal F B')) := by
  intro v
  obtain ⟨β, hβB, d, hdv, hd⟩ := exists_local_gen hB v
  have hd0 : d ≠ 0 := by rintro rfl; exact hdv v.asIdeal.zero_mem
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hB
    rw [eq_bot_iff]
    intro b hb
    have := hd b hb
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    exact (mul_eq_zero.mp this).resolve_left (by simpa using hd0)
  have hβE : algebraMap (𝓞 E) E β ≠ 0 := algebraMap_ne_zero hβ0
  have hσβ : conj F E (algebraMap (𝓞 E) E β) ≠ 0 := by simpa using hβE
  have hδE : algebraMap (𝓞 E) E δ ≠ 0 := algebraMap_ne_zero hδ
  have hσδ : conj F E (algebraMap (𝓞 E) E δ) ≠ 0 := by simpa using hδE
  have hdE : algebraMap F E (algebraMap (𝓞 F) F d) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F E).injective]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hd0
  set u : E := algebraMap (𝓞 E) E β / conj F E (algebraMap (𝓞 E) E β) with hu_def
  have hu : Algebra.norm F u = 1 := by
    rw [norm_div', norm_conj, div_self (Algebra.norm_ne_zero_iff.mpr hβE)]
  have hγ : rotE S hu ∈ orthGroup QD F := rotE_mem S hu
  refine ⟨GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (rotE S hu),
    (orthMap QD (v.adicCompletion F) ⟨rotE S hu, hγ⟩).2, ?_⟩
  rw [← loc_glImage, glImage_rotE]
  refine le_antisymm (loc_le_of_smul_mem v hdv fun z hz => ?_) (loc_le_of_smul_mem v hdv fun x hx => ?_)
  · -- d · u 𝒪_E ⊆ (σδ)⁻¹ B σB'
    rw [mem_latOf, mem_smulLat] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    obtain ⟨ω, -, rfl⟩ := mem_idealLat.mp hy
    -- d σδ ∈ (σβ) σB'
    have hσB : ∀ c ∈ conjIdeal F B, algebraMap (𝓞 F) (𝓞 E) d * c ∈ Ideal.span {conjO F E β} := by
      intro c hc
      obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_of_equiv (conjO F E) c).mp hc
      have := hd b hb
      rw [← conjO_algebraMap (E := E) d, ← map_mul]
      have h' := Ideal.mem_map_of_mem (conjO F E) this
      rwa [Ideal.map_span, Set.image_singleton] at h'
    have hδmem : conjO F E δ ∈ conjIdeal F B * conjIdeal F B' := by
      rw [← conjIdeal_mul, h, conjIdeal_span]; exact Ideal.mem_span_singleton_self _
    have hdδ : algebraMap (𝓞 F) (𝓞 E) d * conjO F E δ ∈ Ideal.span {conjO F E β} * conjIdeal F B' := by
      have hle : Ideal.span {algebraMap (𝓞 F) (𝓞 E) d} * (conjIdeal F B * conjIdeal F B') ≤
          Ideal.span {conjO F E β} * conjIdeal F B' := by
        rw [← mul_assoc]
        refine Ideal.mul_mono_left ?_
        rw [Ideal.span_singleton_mul_le_iff]
        exact hσB
      exact hle (Ideal.mem_span_singleton_mul.mpr ⟨_, hδmem, rfl⟩)
    obtain ⟨μ, hμ, hμe⟩ := Ideal.mem_span_singleton_mul.mp hdδ
    rw [mem_latI]
    refine ⟨β * μ * ω, Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hβB hμ), ?_⟩
    rw [cE_smul_int, ← hyz]
    have e := congrArg (algebraMap (𝓞 E) E) hμe
    rw [map_mul, map_mul, algebraMap_conjO, algebraMap_conjO, algebraMap_O_E] at e
    rw [map_mul, map_mul]
    simp only [RingOfIntegers.coe_eq_algebraMap] at *
    rw [hu_def]
    field_simp
    linear_combination (algebraMap (𝓞 E) E ω) * e
  · -- d · (σδ)⁻¹ B σB' ⊆ u 𝒪_E
    obtain ⟨w, hw, hwx⟩ := (mem_latI S).mp hx
    have hmem : w * conjO F E β ∈ B * Ideal.span {conjO F E δ} := by
      have h1 : w * conjO F E β ∈ B * conjIdeal F B' * conjIdeal F B :=
        Ideal.mul_mem_mul hw (Ideal.mem_map_of_mem _ hβB)
      rwa [mul_assoc, ← conjIdeal_mul, mul_comm B', h, conjIdeal_span] at h1
    obtain ⟨z, hzB, hze⟩ := Ideal.mem_mul_span_singleton.mp hmem
    obtain ⟨κ, hκ⟩ := Ideal.mem_span_singleton'.mp (hd z hzB)
    rw [mem_latOf, mem_smulLat]
    refine ⟨(κ : E), algebraMap_mem_idealLat Submodule.mem_top, ?_⟩
    rw [cE_smul_int, ← hwx]
    have e1 := congrArg (algebraMap (𝓞 E) E) hze
    have e2 := congrArg (algebraMap (𝓞 E) E) hκ
    rw [map_mul, map_mul, algebraMap_conjO, algebraMap_conjO] at e1
    rw [map_mul, map_mul, algebraMap_O_E] at e2
    simp only [RingOfIntegers.coe_eq_algebraMap] at *
    rw [hu_def]
    field_simp
    linear_combination (algebraMap F E (algebraMap (𝓞 F) F d)) * e1 + (conj F E (algebraMap (𝓞 E) E δ)) * e2

/-! ### Every lattice in the genus is a normalized ideal lattice -/

/-- **Every lattice $M$ in the genus of $\mathcal O_E$ is $c^{-1}(d^{-1}\mathfrak A)$ with $N_{E/F}\mathfrak A = (d^2)$.** Here $d \in \mathcal O_F$ clears
denominators ($dM \subseteq \mathcal O_F^2 \subseteq$ `latE`), $\mathfrak A = d\,c(M)$ is an ideal by `genus_mulMat_mem`, and $N\mathfrak A$ (generated by the norms
$N(x) = d^2Q(x)$, `Ideal.relNorm_apply`) is $(d^2)$ because $M$ represents a $\mathfrak p$-unit at every $\mathfrak p$ (`exists_mem_eval_not_mem`). -/
theorem exists_pair_of_genus {M : Submodule (𝓞 F) (Fin 2 → F)} (hML : M.IsLattice F)
    (hM : SameGenus QD (latE S) M) :
    ∃ (d : 𝓞 F) (𝔄 : Ideal (𝓞 E)), d ≠ 0 ∧ 𝔄 ≠ ⊥ ∧ Ideal.relNorm (𝓞 F) 𝔄 = Ideal.span {d ^ 2} ∧
      M = latI S (algebraMap F E (algebraMap (𝓞 F) F d))⁻¹ 𝔄 := by
  have hMi : IsIntegral QD M := SameGenus.isIntegral QD (isIntegral_latE S) hM
  obtain ⟨d, hd, -, h2⟩ := exists_global_bounds hML
  set dE := algebraMap F E (algebraMap (𝓞 F) F d)
  have hdE : dE ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F E).injective]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hd
  have hint : ∀ x ∈ M, dE * cE S x ∈ integralClosure ℤ E := fun x hx => by
    have := (mem_latE S).mp (intVec_le_latE S (h2 x hx))
    rw [cE_smul_int] at this
    exact (mem_integralClosure_iff ℤ E).mpr this
  let 𝔄 : Ideal (𝓞 E) :=
    { carrier := {a | ∃ x ∈ M, (a : E) = dE * cE S x}
      add_mem' := by
        rintro a b ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
        refine ⟨x + y, M.add_mem hx hy, ?_⟩
        rw [cE_add]
        show algebraMap (𝓞 E) E (a + b) = _
        rw [map_add]; change (a : E) + (b : E) = _; rw [hax, hby]; ring
      zero_mem' := ⟨0, M.zero_mem, by rw [cE_zero, mul_zero]; rfl⟩
      smul_mem' := by
        rintro r a ⟨x, hx, hax⟩
        refine ⟨mulMat S (r : E) *ᵥ x, genus_mulMat_mem S hML hM r.2 hx, ?_⟩
        rw [cE_mulMat]
        show algebraMap (𝓞 E) E (r * a) = _
        rw [map_mul]; change (r : E) * (a : E) = _; rw [hax]; ring }
  have hmem𝔄 : ∀ {a : 𝓞 E}, a ∈ 𝔄 ↔ ∃ x ∈ M, (a : E) = dE * cE S x := Iff.rfl
  have hMeq : M = latI S dE⁻¹ 𝔄 := by
    ext z
    rw [mem_latI]
    constructor
    · intro hz
      refine ⟨⟨dE * cE S z, hint z hz⟩, ⟨z, hz, rfl⟩, ?_⟩
      show dE⁻¹ * (dE * cE S z) = cE S z
      field_simp
    · rintro ⟨a, ⟨x, hx, hax⟩, hz⟩
      rw [show algebraMap (𝓞 E) E a = dE * cE S x from hax, ← mul_assoc, inv_mul_cancel₀ hdE, one_mul] at hz
      rwa [← cE_injective S hz]
  -- 𝔄 ≠ ⊥
  have h𝔄 : 𝔄 ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ : ∃ x ∈ M, x ≠ 0 := by
      by_contra hc
      push Not at hc
      have hbot : M = ⊥ := eq_bot_iff.mpr fun x hx => (Submodule.mem_bot _).mpr (hc x hx)
      have := hML.span_eq_top
      rw [hbot, Submodule.bot_coe, Submodule.span_zero_singleton] at this
      have h1 : (Pi.single 0 (1 : F) : Fin 2 → F) ∈ (⊥ : Submodule F (Fin 2 → F)) := this ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at h1
      simpa using congrFun h1 0
    refine (Submodule.ne_bot_iff _).mpr ⟨⟨dE * cE S x, hint x hx⟩, ⟨x, hx, rfl⟩, fun h00 => ?_⟩
    have h0 : dE * cE S x = 0 := congrArg Subtype.val h00
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact hdE h0
    · exact hx0 (cE_injective S (h0.trans (cE_zero S).symm))
  -- the norm of an element of 𝔄
  have hnorm : ∀ x, ∀ a : 𝓞 E, (a : E) = dE * cE S x → ∀ q : 𝓞 F, algebraMap (𝓞 F) F q = (QD).eval x →
      Algebra.intNorm (𝓞 F) (𝓞 E) a = d ^ 2 * q := by
    intro x a hax q hq
    apply RingOfIntegers.coe_injective (K := F)
    rw [Algebra.algebraMap_intNorm (L := E), map_mul, map_pow, hq]
    rw [show algebraMap (𝓞 E) E a = dE * cE S x from hax, map_mul, norm_algebraMap_F, norm_cE_eq_eval]
  refine ⟨d, 𝔄, hd, h𝔄, ?_, hMeq⟩
  rw [Ideal.relNorm_apply]
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    rintro _ ⟨a, ⟨x, hx, hax⟩, rfl⟩
    obtain ⟨q, hq⟩ := hMi x hx
    rw [SetLike.mem_coe, hnorm x a hax q hq]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  · set J := Ideal.span (Algebra.intNorm (𝓞 F) (𝓞 E) '' (𝔄 : Set (𝓞 E)))
    set J'' : Ideal (𝓞 F) := Submodule.comap (LinearMap.mulLeft (𝓞 F) (d ^ 2)) J
    have hJ'' : J'' = ⊤ := by
      by_contra hne
      obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J'' hne
      let w : HeightOneSpectrum (𝓞 F) :=
        ⟨P, hPmax.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hPmax (RingOfIntegers.not_isField F)⟩
      obtain ⟨x, hx, q, hq, hqP⟩ := exists_mem_eval_not_mem S hML hM w
      apply hqP
      apply hJP
      obtain ⟨a, hax⟩ : ∃ a : 𝓞 E, (a : E) = dE * cE S x := ⟨⟨_, hint x hx⟩, rfl⟩
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply, ← hnorm x a hax q hq]
      exact Ideal.subset_span ⟨a, ⟨x, hx, hax⟩, rfl⟩
    rw [Ideal.span_singleton_le_iff_mem]
    have h1 : (1 : 𝓞 F) ∈ J'' := hJ'' ▸ Submodule.mem_top
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_one] at h1
    exact h1

end QuadFormsKB.Tamagawa.BinaryCM
