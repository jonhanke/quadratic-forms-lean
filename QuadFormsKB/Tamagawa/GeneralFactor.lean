/-
# The type sum of a general lattice factors over the primes

**Layer:** the global type set $Y = \{M \in \mathrm{gen}(L) : e_0 \in M\}$ (`CompSet`) for an **arbitrary** integral
lattice $L$ in
the split space $V = (F^{n+1}, \langle m\rangle\perp Q')$, $m \in F^\times$, $Q' = Q_0'\otimes F$ with $Q_0'$ over $\mathcal O_F$; the general local
type sets of `GeneralTypes.lean`.

The lemma `typeSum_eq_prod` factors the type sum $\sum_t w(t)$ over the primes dividing $2m$ when
$L = \mathcal O_F^{n+1}$ and $m \in \mathcal O_F$.
Here $L$ is any lattice and $m$ any nonzero element of $F$:
$$\sum_{t\in O(Q')(\mathbb A_f)\backslash Y} w(t) = \prod_{\mathfrak p \in S} W_\mathfrak p(L_\mathfrak p, 1),\qquad
  S = \{\mathfrak p : L_\mathfrak p \ne \mathfrak o_\mathfrak p^{n+1}\ \text{or}\ |m|_\mathfrak p \ne 1\ \text{or}\ |2|_\mathfrak p \ne 1\}
  \qquad(\texttt{typeSum\_eq\_prodG}),$$
$W_\mathfrak p(\Lambda, c)$ = `locTypeSumG` (local types of the pairs $(M_\mathfrak p, c\,e_0)$, $M_\mathfrak p \in O(V_\mathfrak p)\Lambda$).

**Proves**
* `exists_smul_stdPtG`, `locTypeSumG_std_eq_one`: at $\mathfrak p \notin S$ there is one local type, of weight $1$ (cf.
  `exists_smul_locStdPt` for $m \in F$: one of $Q(x \mp e_0)$ is a unit and its reflection is integral).
* `mem_orbit_compSet_iffG`, `typeEquivG`: global types are the families of local types at the primes of $S$.
* `compWeight_glueCompG`, **`typeSum_eq_prodG`**.

Sources: Weil 1982, §3.4–3.5 [unverified locator]; Kitaoka 1993, §6.8 [unverified]; O'Meara 1963, §92, pp. 246–250 (background). Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.GeneralTypes

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices LocalDensity QuadForm

/-! ### One local type at the standard lattice when $2m$ is a unit -/

section Std

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (m : F) (Q' : QuadForm F n)

local notation "QS" => splitForm m Q'
local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- An integral model of $\langle m\rangle\perp Q'$ from integral models of $m$ and $Q'$. -/
theorem isIntModel_splitForm {Qo' : QuadForm 𝔬 n} (hQo' : IsIntModel v Q' Qo') {mo : 𝔬}
    (hmo : ((mo : 𝔬) : Fv) = algebraMap F Fv m) : IsIntModel v QS (splitForm mo Qo') := by
  intro y
  rw [← Fin.cons_self_tail y]
  have e1 : (fun i => ((Fin.cons (y 0) (Fin.tail y) : Fin (n + 1) → 𝔬) i : Fv)) =
      Fin.cons ((y 0 : 𝔬) : Fv) (fun i => ((Fin.tail y i : 𝔬) : Fv)) := by
    funext i; refine Fin.cases rfl (fun i => rfl) i
  rw [e1, evalIn_splitForm, eval_splitForm_cons, hQo']
  push_cast
  rw [hmo]

/-- The base point $\mathfrak o_\mathfrak p^{n+1} \in Y_\mathfrak p(\mathfrak o_\mathfrak p^{n+1}, 1)$. -/
def stdPtG : LocCompSetG v m Q' (std v) 1 :=
  ⟨std v, ⟨1, locAct_one _⟩, by rw [one_smul]; exact e₀_mem_std v⟩

theorem stabilizer_stdPtG : stabilizer (orthGroup Q' Fv) (stdPtG v m Q') = stdStab Q' v := by
  ext h
  rw [mem_stabilizer_iff, ← mem_stdStab_orthEmb_iff m Q' v h]
  constructor
  · intro hh; exact congrArg Subtype.val hh
  · intro hh; exact Subtype.ext hh

theorem locWeightG_stdPtG : locWeightG v m Q' (stdPtG v m Q') = 1 := by
  simp [locWeightG, stabilizer_stdPtG]

/-- **Transitivity when $2m$ is a unit** (cf. O'Meara 1963, §92, pp. 246–250; `exists_smul_locStdPt` for
$m \in F_\mathfrak p$): given
integral models $Q_o'$ of $Q'$ and $m_o$ of $m$ with $4m_o$ a unit and $\langle m_o\rangle\perp Q_o'$ nondegenerate, $O(Q')(F_\mathfrak p)$ is
transitive on $Y_\mathfrak p(\mathfrak o_\mathfrak p^{n+1}, 1)$. *Proof:* for $M = g\,\mathfrak o_\mathfrak p^{n+1} \ni e_0$, $y = g^{-1}e_0$ is integral with
$Q(y) = m$; the reflection of `exists_refl_e₀` is an integral isometry $\kappa$ with $\kappa e_0 = y$; $g\kappa$ fixes $e_0$, so it is
$\mathrm{diag}(1, h)$ and $M = h\cdot\mathfrak o_\mathfrak p^{n+1}$. -/
@[kb "omeara1963" "§92 (non-dyadic lattices), pp. 246–249"]
theorem exists_smul_stdPtG {Qo' : QuadForm 𝔬 n} (hQo' : IsIntModel v Q' Qo') {mo : 𝔬}
    (hmo : ((mo : 𝔬) : Fv) = algebraMap F Fv m) (h4 : IsUnit (4 * mo))
    (hnd : (splitForm mo Qo').Nondegenerate) (M : LocCompSetG v m Q' (std v) 1) :
    ∃ h : orthGroup Q' Fv, h • stdPtG v m Q' = M := by
  have hQo := isIntModel_splitForm v m Q' hQo' hmo
  have hm : m ≠ 0 := by
    rintro rfl
    rw [map_zero] at hmo
    have : mo = 0 := Subtype.ext hmo
    rw [this, mul_zero] at h4
    exact not_isUnit_zero h4
  have hm2 : algebraMap F Fv (2 * m) ≠ 0 := by
    rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hm
  obtain ⟨⟨g, hgO⟩, hg⟩ := M.2.1
  have he : (e₀ : Fin (n + 1) → Fv) ∈ M.1 := by simpa only [one_smul] using M.2.2
  rw [← hg] at he
  obtain ⟨y, hy, hgy⟩ := he
  replace hgy : g.val *ᵥ y = e₀ := hgy
  obtain ⟨y', rfl⟩ := integral_of_mem_std v hy
  have hQy : (QS).evalIn Fv (fun i => (y' i : Fv)) = algebraMap F Fv m := by
    rw [← evalIn_mulVec_of_mem QS hgO, hgy, evalIn_splitForm_e₀]
  have hQy' : (splitForm mo Qo').eval y' = mo := by
    apply Subtype.ext
    rw [← hQo, hQy, hmo]
  obtain ⟨σ, hσQ, -, hσe⟩ := exists_refl_e₀ h4 Qo' hQy'
  obtain ⟨κ, hκ⟩ := exists_intRep_eq v hQo hnd σ hσQ
  have hκe : ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) =
      fun i => (y' i : Fv) := by
    rw [← coe_e₀_o v, ← coe_intRep_mulVec, hκ, hσe]
  let γ : orthGroup QS Fv := ⟨g, hgO⟩ * κ
  have hγ : (γ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
    show (g * ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv)).val *ᵥ _ = _
    rw [Units.val_mul, ← mulVec_mulVec, hκe, hgy]
  obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 γ hγ
  refine ⟨h, Subtype.ext ?_⟩
  rw [LocCompSetG.smul_val, hh]
  show locAct v (g * ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv)) (std v) = M.1
  rw [locAct_mul, show locAct v ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv) (std v) = std v from κ.2, hg]

/-- **One local type of weight $1$** at the standard lattice when $2m$ is a unit: $W_\mathfrak p(\mathfrak o_\mathfrak p^{n+1}, 1) = 1$. -/
theorem locTypeSumG_std_eq_one (hQ' : Q'.Nondegenerate) {Qo' : QuadForm 𝔬 n} (hQo' : IsIntModel v Q' Qo') {mo : 𝔬}
    (hmo : ((mo : 𝔬) : Fv) = algebraMap F Fv m) (h4 : IsUnit (4 * mo))
    (hnd : (splitForm mo Qo').Nondegenerate) : locTypeSumG v m Q' (std v) 1 = 1 := by
  have hs : ∀ t : LocTypesG v m Q' (std v) 1, t = Quotient.mk'' (stdPtG v m Q') := by
    intro t
    induction t using Quotient.inductionOn' with
    | h M =>
      obtain ⟨g, hg⟩ := exists_smul_stdPtG v m Q' hQo' hmo h4 hnd M
      exact Quotient.sound' ⟨g, hg⟩
  have : Unique (LocTypesG v m Q' (std v) 1) := ⟨⟨Quotient.mk'' (stdPtG v m Q')⟩, hs⟩
  rw [locTypeSumG, finsum_unique]
  obtain ⟨g, hg⟩ := exists_smul_stdPtG v m Q' hQo' hmo h4 hnd (default : LocTypesG v m Q' (std v) 1).out
  rw [← hg, locWeightG_smul v m Q' hQ' (std_isLattice v), locWeightG_stdPtG]

end Std

/-! ### Local components of the global type set of a general lattice -/

section Components

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (m : F) (Q' : QuadForm F n) (L : Lat F (n + 1))

local notation "QS" => splitForm m Q'

/-- **The local component** $M_\mathfrak p \in Y_\mathfrak p(L_\mathfrak p, 1)$ of $M \in Y$. -/
def locOfG (v : HeightOneSpectrum (𝓞 F)) (M : CompSet m Q' L) : LocCompSetG v m Q' (loc v L.1) 1 :=
  ⟨loc v M.1.1, by
      obtain ⟨g, hg, hgM⟩ := M.2.1 v
      exact ⟨⟨g, hg⟩, hgM⟩,
    by rw [one_smul, ← locVec_e₀ v]; exact locVec_mem_loc v M.2.2⟩

theorem locOfG_val (v : HeightOneSpectrum (𝓞 F)) (M : CompSet m Q' L) : (locOfG m Q' L v M).1 = loc v M.1.1 := rfl

theorem locOfG_smul (v : HeightOneSpectrum (𝓞 F)) (h : OAf Q') (M : CompSet m Q' L) :
    locOfG m Q' L v (h • M) = h v • locOfG m Q' L v M :=
  Subtype.ext (loc_latSMul QS (orthEmbAf m Q' h) M.1 v)

/-- **Global orbits are determined prime by prime** (general $L$; as `mem_orbit_compSet_iff`). -/
theorem mem_orbit_compSet_iffG (M M' : CompSet m Q' L) :
    M' ∈ orbit (OAf Q') M ↔
      ∀ v, locOfG m Q' L v M' ∈ orbit (orthGroup Q' (v.adicCompletion F)) (locOfG m Q' L v M) := by
  classical
  constructor
  · rintro ⟨h, rfl⟩ v
    exact ⟨h v, (locOfG_smul m Q' L v h M).symm⟩
  · intro hloc
    choose hv hhv using hloc
    let hp : (v : HeightOneSpectrum (𝓞 F)) → orthGroup Q' (v.adicCompletion F) := fun v =>
      if loc v M.1.1 = loc v M'.1.1 then 1 else hv v
    have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, hp v ∈ stdStab Q' v := by
      filter_upwards [loc_eventually_std M.1.2, loc_eventually_std M'.1.2] with v h1 h2
      have : loc v M.1.1 = loc v M'.1.1 := h1.trans h2.symm
      simp only [hp, this, ↓reduceIte]
      exact (stdStab Q' v).one_mem
    let hA : OAf Q' := ⟨hp, hev⟩
    refine ⟨hA, Subtype.ext (Subtype.ext (loc_injective (hA • M).1.2 M'.1.2 fun v => ?_))⟩
    have e := locOfG_smul m Q' L v hA M
    have e2 : loc v (hA • M).1.1 = (locOfG m Q' L v (hA • M)).1 := rfl
    rw [e2, e]
    show (hp v • locOfG m Q' L v M).1 = _
    simp only [hp]
    split_ifs with heq
    · exact (congrArg Subtype.val (one_smul _ (locOfG m Q' L v M))).trans heq
    · exact congrArg Subtype.val (hhv v)

end Components

/-! ### The factorization -/

section Factor

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (m : F) (Q₀' : QuadForm (𝓞 F) n) (L : Lat F (n + 1))

local notation "QF'" => Q₀'.map (algebraMap (𝓞 F) F)
local notation "QS" => splitForm m (Q₀'.map (algebraMap (𝓞 F) F))

theorem finite_valuation_ne_one {x : F} (hx : x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F x ≠ 1}.Finite := by
  have h1 := Filter.eventually_cofinite.mp (eventually_valuation_le_one (F := F) x)
  have h2 := Filter.eventually_cofinite.mp (eventually_valuation_le_one (F := F) x⁻¹)
  refine (h1.union h2).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq, Set.mem_union, not_le] at hv ⊢
  by_contra hc
  push_neg at hc
  obtain ⟨hle, hle'⟩ := hc
  rw [map_inv₀] at hle'
  have h0 : v.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have := (inv_le_one₀ (zero_lt_iff.mpr h0)).mp hle'
  exact hv (le_antisymm hle this)

/-- **The exceptional primes** of $(L, m)$: $L_\mathfrak p \ne \mathfrak o_\mathfrak p^{n+1}$, $|m|_\mathfrak p \ne 1$ or $|2|_\mathfrak p \ne 1$ (finite). -/
def badSetG (hm : m ≠ 0) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (((Filter.eventually_cofinite.mp (loc_eventually_std L.2)).union
    (finite_valuation_ne_one hm)).union (finite_valuation_ne_one (two_ne_zero (α := F)))).toFinset

theorem not_mem_badSetG (hm : m ≠ 0) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badSetG m L hm) :
    loc v L.1 = std v ∧ v.valuation F m = 1 ∧ v.valuation F 2 = 1 := by
  simp only [badSetG, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  exact ⟨hv.1.1, hv.1.2, hv.2⟩

variable (hm : m ≠ 0)

local notation "S" => badSetG m L hm

/-- At a prime outside $S$, every $M \in Y_\mathfrak p(L_\mathfrak p, 1)$ is in the type of $L_\mathfrak p = \mathfrak o_\mathfrak p^{n+1}$. -/
theorem exists_smul_of_not_mem (hQ' : Q₀'.Nondegenerate) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    (M M' : LocCompSetG v m QF' (loc v L.1) 1) : M' ∈ orbit (orthGroup QF' (v.adicCompletion F)) M := by
  obtain ⟨hL, hmv, h2v⟩ := not_mem_badSetG m L hm hv
  have hmv' : Valued.v (algebraMap F (v.adicCompletion F) m) ≤ 1 := by rw [valued_algebraMap, hmv]
  set mo := toO v _ hmv'
  have hmo : ((mo : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F _ m := rfl
  have hQo' : IsIntModel v QF' (NF.Qp v Q₀') := fun y => evalIn_coe_o v Q₀' y
  have hmo0 : mo ≠ 0 := by
    intro h0
    have : algebraMap F (v.adicCompletion F) m = 0 := by rw [← hmo, h0]; rfl
    exact hm ((map_eq_zero_iff _ (algebraMap F (v.adicCompletion F)).injective).mp this)
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
    exact mul_ne_zero (mul_ne_zero (NF.two_ne_zero' v) hmo0) (NF.nondegenerate_Qp v hQ')
  -- transport to the standard lattice
  have key : ∀ N : LocCompSetG v m QF' (loc v L.1) 1, ∃ h : orthGroup QF' (v.adicCompletion F),
      (h • stdPtG v m QF').1 = N.1 := by
    intro N
    obtain ⟨h, hh⟩ := exists_smul_stdPtG v m QF' hQo' hmo h4 hnd ⟨N.1, by rw [← hL]; exact N.2.1, N.2.2⟩
    exact ⟨h, congrArg Subtype.val hh⟩
  obtain ⟨h, hh⟩ := key M
  obtain ⟨h', hh'⟩ := key M'
  refine ⟨h' * h⁻¹, Subtype.ext ?_⟩
  show locAct v (orthEmb m QF' _ (h' * h⁻¹) : GL (Fin (n + 1)) (v.adicCompletion F)) M.1 = M'.1
  rw [← hh, ← hh', LocCompSetG.smul_val, LocCompSetG.smul_val, ← locAct_mul, ← Subgroup.coe_mul, ← map_mul,
    inv_mul_cancel_right]

/-- **Global types to local types at the primes of $S$**. -/
def typeMapG : orbitRel.Quotient (OAf QF') (CompSet m QF' L) → ((v : S) → LocTypesG v m QF' (loc v L.1) 1) :=
  Quotient.lift (fun M v => Quotient.mk'' (locOfG m QF' L v M)) (fun a b hab => funext fun v => by
    exact Quotient.sound' ((mem_orbit_compSet_iffG m QF' L b a).mp hab v))

theorem typeMapG_mk (M : CompSet m QF' L) (v : S) :
    typeMapG m Q₀' L hm (Quotient.mk'' M) v = Quotient.mk'' (locOfG m QF' L v M) := rfl

theorem typeMapG_injective (hQ' : Q₀'.Nondegenerate) : Function.Injective (typeMapG m Q₀' L hm) := by
  intro t t' h
  induction t using Quotient.inductionOn' with | h M => ?_
  induction t' using Quotient.inductionOn' with | h M' => ?_
  apply Quotient.sound'
  show M ∈ orbit (OAf QF') M'
  rw [mem_orbit_compSet_iffG]
  intro v
  by_cases hv : v ∈ S
  · have := congrFun h ⟨v, hv⟩
    rw [typeMapG_mk, typeMapG_mk] at this
    exact Quotient.exact' this
  · exact exists_smul_of_not_mem m Q₀' L hm hQ' hv _ _

open Classical in
/-- The local family glued from representatives of local types at the primes of $S$ (and $L_\mathfrak p$ elsewhere). -/
def glueFamG (f : (v : S) → LocTypesG v m QF' (loc v L.1) 1) : LocFamily F (n + 1) where
  M v := if hv : v ∈ S then (f ⟨v, hv⟩).out.1 else loc v L.1
  isLattice v := by
    split_ifs with hv
    · obtain ⟨g, hg⟩ := (f ⟨v, hv⟩).out.2.1
      rw [← hg]
      exact locAct_isLattice _ (loc_isLattice v L.2)
    · exact loc_isLattice v L.2
  eventually_std := by
    filter_upwards [(S).finite_toSet.compl_mem_cofinite] with v hv
    have hv' : v ∉ S := hv
    simp only [hv', ↓reduceDIte]
    exact (not_mem_badSetG m L hm hv').1

open Classical in
/-- **The glued lattice** with prescribed local types. -/
def glueCompG (f : (v : S) → LocTypesG v m QF' (loc v L.1) 1) : CompSet m QF' L :=
  ⟨⟨(glueFamG m Q₀' L hm f).glue, (glueFamG m Q₀' L hm f).glue_isLattice⟩, by
      intro v
      rw [LocFamily.loc_glue]
      show ∃ g ∈ _, _ = if hv : v ∈ S then _ else _
      split_ifs with hv
      · obtain ⟨g, hg⟩ := (f ⟨v, hv⟩).out.2.1
        exact ⟨g, g.2, hg⟩
      · exact ⟨1, (orthGroup _ _).one_mem, locAct_one _⟩,
    by
      rw [mem_iff_forall_loc (glueFamG m Q₀' L hm f).glue_isLattice]
      intro v
      rw [LocFamily.loc_glue, locVec_e₀]
      show _ ∈ if hv : v ∈ S then _ else _
      split_ifs with hv
      · simpa only [one_smul] using (f ⟨v, hv⟩).out.2.2
      · rw [(not_mem_badSetG m L hm hv).1]
        exact e₀_mem_std v⟩

theorem locOfG_glueCompG (f : (v : S) → LocTypesG v m QF' (loc v L.1) 1) (v : S) :
    locOfG m QF' L v (glueCompG m Q₀' L hm f) = (f v).out := by
  classical
  apply Subtype.ext
  rw [locOfG_val]
  show loc (v : HeightOneSpectrum (𝓞 F)) (glueFamG m Q₀' L hm f).glue = _
  rw [LocFamily.loc_glue]
  show (if hv : (v : HeightOneSpectrum (𝓞 F)) ∈ S then _ else _) = _
  simp only [v.2, ↓reduceDIte]

theorem locOfG_glueCompG_of_not_mem (f : (v : S) → LocTypesG v m QF' (loc v L.1) 1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : (locOfG m QF' L v (glueCompG m Q₀' L hm f)).1 = std v := by
  classical
  rw [locOfG_val]
  show loc v (glueFamG m Q₀' L hm f).glue = _
  rw [LocFamily.loc_glue]
  show (if hv : v ∈ S then _ else _) = _
  simp only [hv, ↓reduceDIte]
  exact (not_mem_badSetG m L hm hv).1

theorem typeMapG_glueCompG (f : (v : S) → LocTypesG v m QF' (loc v L.1) 1) :
    typeMapG m Q₀' L hm (Quotient.mk'' (glueCompG m Q₀' L hm f)) = f := by
  funext v
  rw [typeMapG_mk, locOfG_glueCompG, Quotient.out_eq']

/-- **Global types = families of local types at the primes of $S$**. -/
def typeEquivG (hQ' : Q₀'.Nondegenerate) :
    orbitRel.Quotient (OAf QF') (CompSet m QF' L) ≃ ((v : S) → LocTypesG v m QF' (loc v L.1) 1) :=
  Equiv.ofBijective _ ⟨typeMapG_injective m Q₀' L hm hQ', fun f => ⟨_, typeMapG_glueCompG m Q₀' L hm f⟩⟩

/-- **The global weight of a glued lattice is the product of the local weights** (`relIndex_restrictedPi`). -/
theorem compWeight_glueCompG (f : (v : S) → LocTypesG v m QF' (loc v L.1) 1) :
    compWeight m QF' L (glueCompG m Q₀' L hm f) = ∏ v : S, locWeightG v m QF' (f v).out := by
  classical
  set y := glueCompG m Q₀' L hm f
  set A' : (v : HeightOneSpectrum (𝓞 F)) → Subgroup (orthGroup QF' (v.adicCompletion F)) :=
    fun v => stabilizer (orthGroup QF' (v.adicCompletion F)) (locOfG m QF' L v y)
  have hA : ∀ v ∉ S, A' v = stdStab QF' v := by
    intro v hv
    simp only [A']
    ext h
    rw [mem_stabilizer_iff, ← mem_stdStab_orthEmb_iff m QF' v h]
    have e := locOfG_glueCompG_of_not_mem m Q₀' L hm f hv
    constructor
    · intro hh
      have := congrArg Subtype.val hh
      rw [LocCompSetG.smul_val, e] at this
      exact this
    · intro hh
      apply Subtype.ext
      rw [LocCompSetG.smul_val, e]
      exact hh
  have hB : ∀ v ∉ S, stdStab QF' v = stdStab QF' v := fun _ _ => rfl
  have hAm : ∀ h, h ∈ stabilizer (OAf QF') y ↔ ∀ v, h v ∈ A' v := by
    intro h
    rw [stabilizer_compSet, Subgroup.mem_comap]
    show (∀ v, _ = _) ↔ _
    refine forall_congr' fun v => ?_
    simp only [A', mem_stabilizer_iff]
    constructor
    · intro hh; exact Subtype.ext hh
    · intro hh; exact congrArg Subtype.val hh
  have hBm : ∀ h, h ∈ locStab QF' (stdLat F n) ↔ ∀ v, h v ∈ stdStab QF' v := mem_locStab_intVec QF'
  have e1 := relIndex_restrictedPi S A' (fun v => stdStab QF' v) hA hB _ _ hAm hBm
  have e2 := relIndex_restrictedPi S (fun v => stdStab QF' v) A' hB hA _ _ hBm hAm
  unfold compWeight
  rw [e1, e2, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib, ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [A', locWeightG]
  rw [locOfG_glueCompG]

/-- **The type sum of a general lattice factors over the exceptional primes** (Weil 1982, §3.5 [unverified locator]): for
$Q = \langle m\rangle\perp Q_0'$ ($m \in F^\times$, $Q_0'$ nondegenerate over $\mathcal O_F$) totally positive definite, $L$ integral and $\mathcal O_F^n$
integral for $Q'$,
$$\sum_{t\in O(Q')(\mathbb A_f)\backslash Y} w(t) = \prod_{\mathfrak p\in S}W_\mathfrak p(L_\mathfrak p, 1),$$
$Y = \{M \in \mathrm{gen}(L) : e_0 \in M\}$, $W_\mathfrak p$ = `locTypeSumG`, $S$ = `badSetG`. -/
@[kb "weil1982" "§3.5 (type sum as a product of local sums, general lattice) [unverified locator]"]
theorem typeSum_eq_prodG (hQ' : Q₀'.Nondegenerate) (hpd : IsTotallyPosDef QS) (hLi : IsIntegral QS L.1)
    (hLi' : IsIntegral QF' (stdLat F n).1) :
    ∑ᶠ t : orbitRel.Quotient (OAf QF') (CompSet m QF' L), typeWeight m QF' L t =
      ∏ v ∈ S, locTypeSumG v m QF' (loc v L.1) 1 := by
  classical
  have hpd' := isTotallyPosDef_of_splitForm hpd
  have hfin := finite_types m QF' L hpd hLi hm
  by_cases hall : ∀ w : S, Nonempty (LocTypesG w m QF' (loc w L.1) 1)
  swap
  · push_neg at hall
    obtain ⟨w₀, hw₀⟩ := hall
    have hR : ∏ v ∈ S, locTypeSumG v m QF' (loc v L.1) 1 = 0 := by
      refine Finset.prod_eq_zero w₀.2 ?_
      rw [locTypeSumG, finsum_of_isEmpty]
    have hE : IsEmpty (orbitRel.Quotient (OAf QF') (CompSet m QF' L)) :=
      ⟨fun t => hw₀.false (typeMapG m Q₀' L hm t w₀)⟩
    rw [hR, finsum_of_isEmpty]
  have hfinP : Finite ((v : S) → LocTypesG v m QF' (loc v L.1) 1) :=
    Finite.of_equiv _ (typeEquivG m Q₀' L hm hQ')
  have hfinv : ∀ v : S, Finite (LocTypesG v m QF' (loc v L.1) 1) := by
    intro v
    let f₀ : (w : S) → LocTypesG w m QF' (loc w L.1) 1 := fun w => Classical.choice (hall w)
    exact Finite.of_injective (fun x => Function.update f₀ v x) (Function.update_injective f₀ v)
  let _ : Fintype (orbitRel.Quotient (OAf QF') (CompSet m QF' L)) := Fintype.ofFinite _
  let _ : ∀ v : S, Fintype (LocTypesG v m QF' (loc v L.1) 1) := fun v => Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have step : ∀ t, typeWeight m QF' L t =
      compWeight m QF' L (glueCompG m Q₀' L hm (typeEquivG m Q₀' L hm hQ' t)) := by
    intro t
    rw [typeWeight_eq_compWeight]
    refine compWeight_of_mem_orbit m QF' L hpd' hLi' ?_
    have h1 : (Quotient.mk'' (glueCompG m Q₀' L hm (typeEquivG m Q₀' L hm hQ' t)) :
        orbitRel.Quotient (OAf QF') (CompSet m QF' L)) = t :=
      typeMapG_injective m Q₀' L hm hQ' (typeMapG_glueCompG m Q₀' L hm _)
    have h2 : (Quotient.mk'' t.out : orbitRel.Quotient (OAf QF') (CompSet m QF' L)) =
        Quotient.mk'' (glueCompG m Q₀' L hm (typeEquivG m Q₀' L hm hQ' t)) := by
      rw [h1, Quotient.out_eq']
    exact Quotient.exact' h2
  rw [Finset.sum_congr rfl fun t _ => step t,
    Equiv.sum_comp (typeEquivG m Q₀' L hm hQ') (fun f => compWeight m QF' L (glueCompG m Q₀' L hm f))]
  simp_rw [compWeight_glueCompG]
  rw [← Finset.prod_coe_sort S]
  simp_rw [locTypeSumG, finsum_eq_sum_of_fintype]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end Factor

end QuadFormsKB.Tamagawa
