/-
# O'Meara 102:7, 102:7a, 102:8a: the number of proper spinor genera as an idèle index

**Layer:** $V = F^n$ over a number field $F$ with a regular form `Q : QuadForm F n`, lattices `Lat F n`, $S$ = all
finite spots. The adelic orthogonal group $O(V)(\mathbb A_f)$ = `OAf Q`, its rotation idèles $J_V$ = `Tamagawa.soAf Q`
(every component a rotation), the adelic spinor kernel $J'_V$ = `spinorKernelAf Q`, the group $P_VJ'_V$ =
`spnPlusGroup Q` (`Sec102.lean`), the stabilizer $O(\hat L)$ = `locStab Q L`; the idèle group $J_F$ =
`IdeleGroup (𝓞 F) F` with components `OMeara.ideleAt`, $D = \theta(O^+(V))$ = `spinorNormGroup Q hQ`, $P_D$ =
`principalSpinorIdeles Q hQ` (`Sec101BD.lean`).

**Defines**
* `spnPlusLocGroup Q L` $= P_VJ'_VO(\hat L) \le O(V)(\mathbb A_f)$;
* `localSpinorNormSq Q hQ v L` $= \theta(O^+(L_\mathfrak p))$ as a subgroup of $F_\mathfrak p^\times/F_\mathfrak p^{\times2}$;
* `spinorIdeles Q hQ L` $= J_F^L$, O'Meara's group of idèles $i$ with $i_\mathfrak p \in \theta(O^+(L_\mathfrak p))$ at every
  finite spot (no condition at the infinite spots): the preimage of `spinorIdeleGroup` (`Sec101D.lean`, finite idèles)
  under $J_F \to$ finite idèles;
* `spinorIdeleMap Q hQ L`: O'Meara's homomorphism $\Phi\colon J_V \to J_F/P_DJ_F^L$ of the proof of 102:7, step 3.

**Proves** (O'Meara 1973, §102B, pp. 300–304)
* `properSpinorGenusNumber_eq_index`: $g^+(L) = (O(V)(\mathbb A_f) : P_VJ'_VO(\hat L))$ (proof of 102:7, steps 1–2),
  and `properSpinorGenusNumber_eq_index_soAf`: $g^+(L) = (J_V : J'_VP_VJ_L)$ with $J_V$ the rotation idèles, O'Meara's
  formula;
* `ker_spinorIdeleMap`: $\ker\Phi = J'_VP_VJ_L$; `spinorIdeleMap_surjective`: $\Phi$ is onto for $n \ge 3$
 ;
* **`omeara102_7`** (Theorem 102:7): $g^+(L) = (J_F : P_DJ_F^L)$ if $n \ge 3$;
* **`omeara102_7a`** (Corollary 102:7a): for every $n$, $g^+(L) = (J_V : J'_VP_VJ_L)$ and $g^+(L)$ divides
  $(J_F : P_DJ_F^L)$;
* **`omeara102_8a`** (Corollary 102:8a, and the first assertion of 102:8): $g^+(L)$ is a power of $2$, for every $n$.

All unconditional. *Deviation.* $J_V$ here has no components at the infinite spots (the library's adelic groups are
finite-adelic); since O'Meara's $J_L$ contains all of $\prod_{\mathfrak p \in \Omega - S}O^+(V_\mathfrak p)$, the
indices are the same. Indices are `Subgroup.index`, and $g^+(L)$ = `properSpinorGenusNumber` is a `Set.ncard`; both
are $0$ for an infinite count, so the equalities hold as stated without a finiteness hypothesis (both sides are in fact
finite, `genusProperSpinorGenera_finite`).
-/
import QuadFormsKB.Literature.OMeara.Sec104Nine
import QuadFormsKB.Literature.OMeara.Sec102Spn
import QuadFormsKB.Literature.OMeara.Sec101D
import QuadFormsKB.Literature.Hanke2005.SpinorIdele
import QuadFormsKB.Literature.Hanke2005.SpinorSurjLocal
import QuadFormsKB.Literature.OMeara.Sec101Ten
import QuadFormsKB.Literature.OMeara.Sec104Bridge
import QuadFormsKB.Literature.OMeara.Sec104LocalMod

open NumberField IsDedekindDomain Matrix
open QuadFormsKB.OMeara (ideleAt ideleAt_mul ideleAt_one ideleAt_inv ideleAt_ofAdic_self ideleAt_ofAdic_ne)
open QuadFormsKB.Hanke2005.SpinorIdele (ideleAt_ne_zero sqClassOf_inv ideleAtHom ideleAt_unitEmbedding spinorNorm_one')

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

local notation "J" => IdeleGroup (𝓞 F) F

/-! ### Double cosets modulo a normal subgroup -/

/-- For $N$ normal in $G$: $N\backslash G/H \simeq G/(N \sqcup H)$. -/
def dosetEquivQuotOfNormal {G : Type*} [Group G] (N H : Subgroup G) [N.Normal] :
    DoubleCoset.Quotient (N : Set G) H ≃ G ⧸ (N ⊔ H) :=
  Quotient.congr (Equiv.refl _) fun g g' => by
    rw [Equiv.refl_apply, Equiv.refl_apply, doset_rel_iff_of_normal, QuotientGroup.leftRel_apply]

/-! ### The proper spinor genera in a genus as a quotient group -/

/-- **The group $P_VJ'_VJ_L$** (O'Meara 1973, §102B, proof of 102:7, step 1, p. 301), here
$O^+(V)\,O'(V_{\mathbb A_f})\,O(\hat L) \le O(V)(\mathbb A_f)$. -/
@[kb "omeara1963" "§102B, proof of 102:7, step 1, p. 301 (the group J'_V P_V J_L)"]
def spnPlusLocGroup (L : Lat F n) : Subgroup (OAf Q) := spnPlusGroup Q ⊔ locStab Q L

theorem spnPlusLocGroup_normal (hQ : Q.Nondegenerate) (L : Lat F n) : (spnPlusLocGroup Q L).Normal :=
  normal_of_spinorKernelAf_le Q hQ (le_sup_right.trans le_sup_left)

/-- The proper spinor genera in $\operatorname{gen}L$ are the classes of the `spnPlusGroup`-orbits on the genus. -/
def genusProperSpinorGeneraEquivOrbits (L : Lat F n) :
    @AWS.ClassesInGenus (OAf Q) (Lat F n) _ (latAction Q) (spnPlusGroup Q) L ≃ genusProperSpinorGenera Q L := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  refine Equiv.ofBijective
    (Quotient.lift (fun M => (⟨Quotient.mk (properSpnSetoid Q) (M : Lat F n), M, rfl, ?_⟩ :
      genusProperSpinorGenera Q L)) fun M M' h => Subtype.ext (Quotient.sound h)) ⟨?_, ?_⟩
  · exact (Set.ext_iff.mp (orbit_eq_genus Q L) M).mp M.2
  · intro x y hxy
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    have h := congrArg Subtype.val hxy
    simp only [Quotient.lift_mk] at h
    have h2 := Quotient.exact h
    exact Quotient.sound h2
  · rintro ⟨_, M, rfl, hM⟩
    have hM' : M ∈ @MulAction.orbit (OAf Q) (Lat F n) (latAction Q).toSMul L := by
      rw [orbit_eq_genus]; exact hM
    exact ⟨Quotient.mk _ ⟨M, hM'⟩, rfl⟩

/-- **The proper spinor genera in $\operatorname{gen}L$ form the group $O(V)(\mathbb A_f)/P_VJ'_VO(\hat L)$**
(O'Meara 1973, §102B, proof of 102:7, steps 1–2, pp. 300–301). -/
@[kb "omeara1963" "§102B, proof of 102:7, steps 1–2, pp. 300–301"]
def genusProperSpinorGeneraEquiv (hQ : Q.Nondegenerate) (L : Lat F n) :
    genusProperSpinorGenera Q L ≃ OAf Q ⧸ spnPlusLocGroup Q L := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  have := spnPlusGroup_normal Q hQ
  refine (genusProperSpinorGeneraEquivOrbits Q L).symm.trans ?_
  have e := AWS.dosetEquivClasses (spnPlusGroup Q) L
  rw [stabilizer_eq_locStab Q L] at e
  exact e.symm.trans (dosetEquivQuotOfNormal _ _)

/-- **$g^+(L) = (O(V)(\mathbb A_f) : P_VJ'_VO(\hat L))$** (O'Meara 1973, §102B, proof of 102:7, step 2, p. 301). -/
@[kb "omeara1963" "§102B, proof of 102:7, step 2, p. 301 (g⁺(L) = (J_V : J'_V P_V J_L))"]
theorem properSpinorGenusNumber_eq_index (hQ : Q.Nondegenerate) (L : Lat F n) :
    properSpinorGenusNumber Q L = (spnPlusLocGroup Q L).index := by
  rw [properSpinorGenusNumber, ← Nat.card_coe_set_eq, Subgroup.index]
  exact Nat.card_congr (genusProperSpinorGeneraEquiv Q hQ L)

/-! ### Reduction to rotation idèles -/

/-- Every adelic isometry is a rotation idèle times an element of $O(\hat L)$ (O'Meara's $J_V$ consists of rotations;
`exists_oaf_soSub`). -/
theorem exists_soAf_mul_locStab (hQ : Q.Nondegenerate) (L : Lat F n) (g : OAf Q) :
    ∃ r ∈ Tamagawa.soAf Q, r⁻¹ * g ∈ locStab Q L := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  have hg : SameGenus Q L.1 (latSMul Q g L).1 := by
    have : latSMul Q g L ∈ MulAction.orbit (OAf Q) L := ⟨g, rfl⟩
    rw [orbit_eq_genus] at this
    exact this
  obtain ⟨r, hr, hrL⟩ := exists_oaf_soSub hQ L hg
  refine ⟨r, hr, ?_⟩
  rw [← stabilizer_eq_locStab, MulAction.mem_stabilizer_iff, mul_smul]
  change r⁻¹ • latSMul Q g L = L
  rw [← hrL]
  exact inv_smul_smul r L

/-- **$g^+(L) = (J_V : J'_VP_VJ_L)$ with $J_V$ the rotation idèles** (O'Meara 1973, §102B, proof of 102:7, step 2,
p. 301, and 102:7a, p. 302): the index of $J_V \cap P_VJ'_VO(\hat L)$ in the group $J_V$ = `Tamagawa.soAf Q` of
adelic isometries all of whose components are rotations. -/
@[kb "omeara1963" "§102B, 102:7a, p. 302 (g⁺(L) = (J_V : J'_V P_V J_L))"]
theorem properSpinorGenusNumber_eq_index_soAf (hQ : Q.Nondegenerate) (L : Lat F n) :
    properSpinorGenusNumber Q L = ((spnPlusLocGroup Q L).subgroupOf (Tamagawa.soAf Q)).index := by
  rw [properSpinorGenusNumber_eq_index Q hQ L]
  have := spnPlusLocGroup_normal Q hQ L
  let f : Tamagawa.soAf Q →* OAf Q ⧸ spnPlusLocGroup Q L :=
    (QuotientGroup.mk' (spnPlusLocGroup Q L)).comp (Tamagawa.soAf Q).subtype
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨r, hr, hrg⟩ := exists_soAf_mul_locStab Q hQ L g
      refine ⟨⟨r, hr⟩, ?_⟩
      change (QuotientGroup.mk r : OAf Q ⧸ spnPlusLocGroup Q L) = QuotientGroup.mk g
      rw [QuotientGroup.eq]
      exact Subgroup.mem_sup_right hrg
  have hker : f.ker = (spnPlusLocGroup Q L).subgroupOf (Tamagawa.soAf Q) := by
    ext x
    simp [f, Subgroup.mem_subgroupOf]
  rw [Subgroup.index, Subgroup.index, ← hker]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).symm

/-! ### Units are spinor norms of $O^+(L_\mathfrak p)$ at almost all spots -/

section Good

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **$\mathfrak o_\mathfrak p^n$ is unimodular** at a spot where the matrix $G$ of the standard base is integral with
unit determinant (the version of `isUnimodular_std` with integral entries). -/
theorem isUnimodular_std_of_le (hn : 0 < n)
    (hG : ∀ i j, v.valuation F (OMeara.gram Q.toQuadraticForm (fun i => (Pi.single i 1 : Fin n → F)) i j) ≤ 1)
    (hd : v.valuation F (OMeara.gram Q.toQuadraticForm (fun i => (Pi.single i 1 : Fin n → F))).det = 1) :
    OMeara.IsUnimodular (qk Q Fv) (std v : Submodule 𝔬 (Fin n → Fv)) := by
  classical
  set G := OMeara.gram Q.toQuadraticForm (fun i => (Pi.single i 1 : Fin n → F)) with hGdef
  have hmem : ∀ i j, algebraMap F Fv (G i j) ∈ v.adicCompletionIntegers F := fun i j => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
    exact hG i j
  let U : Matrix (Fin n) (Fin n) 𝔬 := fun i j => ⟨algebraMap F Fv (G i j), hmem i j⟩
  have hU : U.map (algebraMap 𝔬 Fv) = G.map (algebraMap F Fv) := rfl
  let b0 := Module.Basis.span (OMeara.linearIndependent_single 𝔬 (F := Fv) (ι := Fin n))
  let b : Module.Basis (Fin n) 𝔬 (std v : Submodule 𝔬 (Fin n → Fv)) :=
    b0.map (LinearEquiv.ofEq _ _ (std_eq_matLat v).symm)
  have hb : ∀ i, (b i : Fin n → Fv) = Pi.single i 1 := fun i => by
    simp only [b, Module.Basis.map_apply]
    exact congrArg Subtype.val (Module.Basis.span_apply _ i)
  rw [OMeara.isUnimodular_iff_gram (qk Q Fv) b]
  refine ⟨⟨⟨0, hn⟩⟩, U, ?_, ?_⟩
  · rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have : ((U.det : 𝔬) : Fv) = (G.map (algebraMap F Fv)).det := by
      rw [← hU]
      exact RingHom.map_det (algebraMap 𝔬 Fv) U
    rw [this, show (G.map (algebraMap F Fv)).det = algebraMap F Fv G.det from (RingHom.map_det _ G).symm,
      valued_algebraMap, hd]
  · rw [hU, ← gram_qk_single]
    simp only [hb]

/-- **Good spots**: $\mathfrak p$ non-dyadic, $L_\mathfrak p = \mathfrak o_\mathfrak p^n$, and the matrix of the standard
base integral with unit determinant at $\mathfrak p$. All but finitely many spots are good (`eventually_goodSpot`). -/
def GoodSpot (L : Lat F n) : Prop :=
  IsUnit (2 : 𝔬) ∧ loc v L.1 = std v ∧
    (∀ i j, v.valuation F (OMeara.gram Q.toQuadraticForm (fun i => (Pi.single i 1 : Fin n → F)) i j) ≤ 1) ∧
    v.valuation F (OMeara.gram Q.toQuadraticForm (fun i => (Pi.single i 1 : Fin n → F))).det = 1

/-- **At a good spot, $\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$** (O'Meara 1973, 92:5: $L_\mathfrak p$ is
unimodular and $\mathfrak p$ non-dyadic), for $n \ge 2$. -/
theorem spinorNormsContainUnits_of_goodSpot (hQ : Q.Nondegenerate) (hn : 2 ≤ n) (L : Lat F n)
    (hv : GoodSpot Q v L) : SpinorNormsContainUnits Q v L := by
  obtain ⟨h2, hL, hG, hd⟩ := hv
  apply spinorNormsContainUnits_of_omeara Q v hQ L
  intro ε hε
  have hU := isUnimodular_std_of_le Q v (by omega) hG hd
  have hmod : OMeara.IsModular (qk Q Fv) (𝔬 ∙ (1 : Fv)) (loc v L.1) := by
    have : (𝔬 ∙ (1 : Fv)) = 1 := (Submodule.one_eq_span).symm
    rw [this, hL]; exact hU
  have hrk : Module.finrank 𝔬 (loc v L.1) = n := finrank_loc v L
  exact OMeara.exists_hasSpinorNorm_of_isModular (qk Q Fv) h2 (loc_fg v L) hmod (by omega) hε

end Good

theorem eventually_isUnit_two :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, IsUnit (2 : v.adicCompletionIntegers F) := by
  filter_upwards [eventually_not_mem (show (2 : 𝓞 F) ≠ 0 from two_ne_zero)] with v hv
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have e : ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap (𝓞 F) (v.adicCompletion F) 2 := by rw [map_ofNat]; rfl
  rw [e, valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff.mpr hv]

/-- All but finitely many spots are good. -/
theorem eventually_goodSpot (hQ : Q.Nondegenerate) (L : Lat F n) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, GoodSpot Q v L := by
  have hG : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j,
      v.valuation F (OMeara.gram Q.toQuadraticForm (fun i => (Pi.single i 1 : Fin n → F)) i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    exact fun i j => eventually_valuation_le_one _
  filter_upwards [eventually_isUnit_two, loc_eventually_std L.2, hG,
    eventually_valuation_eq_one (det_gram_single_ne_zero Q hQ)] with v h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-! ### The idèle group $J_F^L$ and the homomorphism $\Phi$ -/

section Idele

variable (hQ : Q.Nondegenerate)

/-- **$\theta(O^+(L_\mathfrak p))$ as a group of square classes** (O'Meara 1973, §101D, p. 297): the spinor norms of the
rotations of $V_\mathfrak p$ carrying $L_\mathfrak p$ onto itself, in $F_\mathfrak p^\times/F_\mathfrak p^{\times 2}$
(`localSpinorNormGroup` is its preimage in $F_\mathfrak p^\times$). -/
def localSpinorNormSq (v : HeightOneSpectrum (𝓞 F)) (L : Lat F n) : Subgroup (SqClass (v.adicCompletion F)) :=
  (locStabV Q v L ⊓ Tamagawa.soSub Q (v.adicCompletion F)).map (spinorNormHom Q (v.adicCompletion F) hQ)

theorem mem_localSpinorNormSq {v : HeightOneSpectrum (𝓞 F)} {L : Lat F n} {c : SqClass (v.adicCompletion F)} :
    c ∈ localSpinorNormSq Q hQ v L ↔
      ∃ g ∈ locStabV Q v L ⊓ Tamagawa.soSub Q (v.adicCompletion F), spinorNorm Q (v.adicCompletion F) g = c := by
  simp [localSpinorNormSq, spinorNormHom_apply]

/-- **The idèle group $J_F^L$** (O'Meara 1973, §101D, p. 297, item 101.d1), as a subgroup of the full idèle group
$J_F$ = `IdeleGroup (𝓞 F) F`: the idèles $i$ with $i_\mathfrak p \in \theta(O^+(L_\mathfrak p))$ at every finite spot
$\mathfrak p$ and no condition at the infinite spots. It is the preimage of `spinorIdeleGroup` (the same condition on
finite idèles) under the projection of $J_F$ onto the finite idèles (`mem_spinorIdeles`). -/
@[kb "omeara1963" "§101D, p. 297 (the idèle group J_F^L)"]
def spinorIdeles (L : Lat F n) : Subgroup J :=
  (spinorIdeleGroup Q hQ L).comap
    (Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom)

theorem mem_spinorIdeles {L : Lat F n} {i : J} :
    i ∈ spinorIdeles Q hQ L ↔ ∀ v, sqClassOf (ideleAt i v) ∈ localSpinorNormSq Q hQ v L := by
  refine forall_congr' fun v => ?_
  rw [sqClassOf_of_ne_zero (ideleAt_ne_zero i v)]
  rw [localSpinorNormGroup, Subgroup.mem_comap, sqClassHom_apply]
  exact Iff.of_eq (congrArg (· ∈ localSpinorNormSq Q hQ v L) (congrArg SqClass.mk (Units.ext rfl)))

/-- **$P_DJ_F^L$** (O'Meara 1973, §102B, 102:7, p. 300). -/
@[kb "omeara1963" "§102B, 102:7, p. 300 (the group P_D J_F^L)"]
def principalSpinorIdelesSup (L : Lat F n) : Subgroup J := principalSpinorIdeles Q hQ ⊔ spinorIdeles Q hQ L

/-- **$i$ is associated with $\Sigma$** (O'Meara 1973, §102B, proof of 102:7, step 3, p. 301), for a rotation idèle
$\Sigma \in J_V$ and an idèle $i$: $i_\mathfrak p \in \theta(\Sigma_\mathfrak p)\,\theta(O^+(L_\mathfrak p))$ at every
finite spot (O'Meara takes $i_\mathfrak p \in \theta(\Sigma_\mathfrak p)$; the factor $\theta(O^+(L_\mathfrak p))$ only
changes $i$ modulo $J_F^L$). -/
def SpinorIdeleAssoc (L : Lat F n) (b : Tamagawa.soAf Q) (x : J) : Prop :=
  ∀ v, sqClassOf (ideleAt x v) * spinorNorm Q (v.adicCompletion F) ((b : OAf Q) v) ∈ localSpinorNormSq Q hQ v L

variable {Q hQ}

theorem spinorIdeleAssoc_mul {L : Lat F n} {b b' : Tamagawa.soAf Q} {x y : J}
    (h : SpinorIdeleAssoc Q hQ L b x) (h' : SpinorIdeleAssoc Q hQ L b' y) :
    SpinorIdeleAssoc Q hQ L (b * b') (x * y) := by
  intro v
  have e : ((b * b' : Tamagawa.soAf Q) : OAf Q) v = (b : OAf Q) v * (b' : OAf Q) v := rfl
  rw [ideleAt_mul, sqClassOf_mul (ideleAt_ne_zero x v) (ideleAt_ne_zero y v), e,
    ← spinorNormHom_apply Q _ hQ, map_mul, spinorNormHom_apply, spinorNormHom_apply]
  have := Subgroup.mul_mem _ (h v) (h' v)
  convert this using 1
  ac_rfl

theorem inv_mul_mem_spinorIdeles_of_assoc {L : Lat F n} {b : Tamagawa.soAf Q} {x y : J}
    (h : SpinorIdeleAssoc Q hQ L b x) (h' : SpinorIdeleAssoc Q hQ L b y) : x⁻¹ * y ∈ spinorIdeles Q hQ L := by
  rw [mem_spinorIdeles]
  intro v
  rw [ideleAt_mul, ideleAt_inv, sqClassOf_mul (inv_ne_zero (ideleAt_ne_zero x v)) (ideleAt_ne_zero y v),
    sqClassOf_inv]
  have := Subgroup.mul_mem _ (h v) (h' v)
  convert this using 1
  set s := spinorNorm Q (v.adicCompletion F) ((b : OAf Q) v)
  calc sqClassOf (ideleAt x v) * sqClassOf (ideleAt y v)
      = sqClassOf (ideleAt x v) * sqClassOf (ideleAt y v) * (s * s) := by rw [SqClass.mul_self, mul_one]
    _ = _ := by ac_rfl

theorem spinorIdeleAssoc_one_iff {L : Lat F n} (x : J) :
    SpinorIdeleAssoc Q hQ L 1 x ↔ x ∈ spinorIdeles Q hQ L := by
  rw [mem_spinorIdeles]
  refine forall_congr' fun v => ?_
  rw [show ((1 : Tamagawa.soAf Q) : OAf Q) v = 1 from rfl, spinorNorm_one' Q hQ, mul_one]

/-- **Every rotation idèle has an associated idèle** (O'Meara 1973, §102B, proof of 102:7, step 3, p. 301): take
$i_\mathfrak p$ representing $\theta(\Sigma_\mathfrak p)$ at the finitely many $\mathfrak p$ with
$\Sigma_\mathfrak p \notin O(L_\mathfrak p)$, and $i_\mathfrak p = 1$ elsewhere. -/
theorem exists_spinorIdeleAssoc (L : Lat F n) (b : Tamagawa.soAf Q) : ∃ x : J, SpinorIdeleAssoc Q hQ L b x := by
  classical
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : v.adicCompletion F, c ≠ 0 ∧
      spinorNorm Q (v.adicCompletion F) ((b : OAf Q) v) = sqClassOf c := by
    intro v
    obtain ⟨xs, hxs, hxe⟩ := exists_symmProd_eq Q (v.adicCompletion F) hQ ((b : OAf Q) v)
    exact ⟨_, valProd_ne_zero Q _ hxs, by rw [← hxe, spinorNorm_symmProd Q _ hQ xs hxs]⟩
  choose c hc0 hcσ using hc
  have hfin : {v | (b : OAf Q) v ∉ locStabV Q v L}.Finite := by
    refine ((Filter.eventually_cofinite.mp (b : OAf Q).2).union
      (Filter.eventually_cofinite.mp (loc_eventually_std L.2))).subset ?_
    intro v hv
    by_contra hc'
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc'
    exact hv ((locStabV_eq_stdStab Q v L hc'.2).mpr hc'.1)
  set S := hfin.toFinset
  let x : J := ∏ v ∈ S, IdeleGroup.ofAdicCompletion (𝓞 F) F v (Units.mk0 (c v) (hc0 v))
  have hxv : ∀ v, ideleAt x v = if v ∈ S then c v else 1 := by
    intro v
    change ideleAtHom v x = _
    simp only [x, map_prod]
    split_ifs with hv
    · rw [Finset.prod_eq_single_of_mem v hv]
      · exact ideleAt_ofAdic_self v _
      · intro v' _ hv'
        exact ideleAt_ofAdic_ne v' v (Ne.symm hv') _
    · refine Finset.prod_eq_one fun v' hv' => ?_
      exact ideleAt_ofAdic_ne v' v (fun h => hv (h ▸ hv')) _
  refine ⟨x, fun v => ?_⟩
  rw [hxv]
  split_ifs with hv
  · rw [hcσ, SqClass.mul_self]; exact Subgroup.one_mem _
  · rw [sqClassOf_one, one_mul, mem_localSpinorNormSq]
    refine ⟨(b : OAf Q) v, ⟨?_, b.2 v⟩, rfl⟩
    by_contra hc'
    exact hv (hfin.mem_toFinset.mpr hc')

variable (Q hQ)

/-- **O'Meara's homomorphism $\Phi\colon J_V \to J_F/P_DJ_F^L$** (O'Meara 1973, §102B, proof of 102:7, step 3,
p. 301): $\Sigma \mapsto$ the class of any idèle associated with $\Sigma$ (`spinorIdeleMap_eq`). -/
@[kb "omeara1963" "§102B, proof of 102:7, step 3, p. 301 (the homomorphism Φ : J_V → J_F/P_D J_F^L)"]
def spinorIdeleMap (L : Lat F n) : Tamagawa.soAf Q →* J ⧸ principalSpinorIdelesSup Q hQ L where
  toFun b := QuotientGroup.mk (exists_spinorIdeleAssoc (hQ := hQ) L b).choose
  map_one' := by
    rw [← QuotientGroup.mk_one, QuotientGroup.eq]
    refine Subgroup.mem_sup_right ?_
    have := (exists_spinorIdeleAssoc (hQ := hQ) L 1).choose_spec
    rw [spinorIdeleAssoc_one_iff] at this
    simpa using this
  map_mul' b b' := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact Subgroup.mem_sup_right (inv_mul_mem_spinorIdeles_of_assoc
      (exists_spinorIdeleAssoc (hQ := hQ) L (b * b')).choose_spec
      (spinorIdeleAssoc_mul (exists_spinorIdeleAssoc (hQ := hQ) L b).choose_spec
        (exists_spinorIdeleAssoc (hQ := hQ) L b').choose_spec))

variable {Q hQ}

/-- $\Phi(\Sigma)$ is the class of any idèle associated with $\Sigma$. -/
theorem spinorIdeleMap_eq {L : Lat F n} {b : Tamagawa.soAf Q} {x : J} (h : SpinorIdeleAssoc Q hQ L b x) :
    spinorIdeleMap Q hQ L b = QuotientGroup.mk x := by
  change QuotientGroup.mk _ = _
  rw [QuotientGroup.eq]
  exact Subgroup.mem_sup_right
    (inv_mul_mem_spinorIdeles_of_assoc (exists_spinorIdeleAssoc (hQ := hQ) L b).choose_spec h)

end Idele

/-! ### The kernel and the image of $\Phi$ -/

section KernelImage

variable {Q}

theorem spinorKernel_le_soSub' (hQ : Q.Nondegenerate) (K : Type) [Field K] [Algebra F K] [CharZero K] :
    spinorKernel Q K ≤ Tamagawa.soSub Q K := by
  intro k hk
  rw [spinorKernel_eq_ker Q K hQ] at hk
  have hk1 : detHom Q K k = 1 := (Subgroup.mem_inf.mp hk).2
  rw [Tamagawa.mem_soSub, ← detHom_val, hk1, Units.val_one]

theorem spnPlusGroup_le_soAf (hQ : Q.Nondegenerate) : spnPlusGroup Q ≤ Tamagawa.soAf Q := by
  refine sup_le ?_ fun k hk v => spinorKernel_le_soSub' hQ _ (hk v)
  rintro _ ⟨γ, hγ, rfl⟩ v
  exact orthMap_mem_soSub (Q := Q) (v.adicCompletion F) hγ

variable (hQ : Q.Nondegenerate)

/-- **The kernel of $\Phi$ is $J'_VP_VJ_L$** (O'Meara 1973, §102B, proof of 102:7, step 5, p. 302, "we leave it to
the reader to verify that $J'_VP_VJ_L$ is the entire kernel"): for a rotation idèle $\Sigma$, $\Phi(\Sigma) = 1$ if and
only if $\Sigma \in P_VJ'_VO(\hat L)$. *Proof of $\subseteq$:* if $i = (\alpha)j$ is associated with $\Sigma$,
$\alpha = \theta(\gamma)$ with $\gamma \in O^+(V)$, then $\theta((\gamma^{-1}\Sigma)_\mathfrak p) \in
\theta(O^+(L_\mathfrak p))$ at every $\mathfrak p$; choosing $\rho_\mathfrak p \in O^+(L_\mathfrak p)$ with the same spinor
norm ($\rho_\mathfrak p = (\gamma^{-1}\Sigma)_\mathfrak p$ when this lies in $O(L_\mathfrak p)$) gives
$\gamma^{-1}\Sigma\rho^{-1} \in J'_V$. No dimension hypothesis. -/
@[kb "omeara1963" "§102B, proof of 102:7, step 5, p. 302 (the kernel of Φ is J'_V P_V J_L)"]
theorem ker_spinorIdeleMap (L : Lat F n) :
    (spinorIdeleMap Q hQ L).ker = (spnPlusLocGroup Q L).subgroupOf (Tamagawa.soAf Q) := by
  classical
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hb
    obtain ⟨x, hx⟩ := exists_spinorIdeleAssoc (hQ := hQ) L b
    rw [spinorIdeleMap_eq hx, ← QuotientGroup.mk_one, QuotientGroup.eq, mul_one, inv_mem_iff] at hb
    obtain ⟨p, hp, j, hj, rfl⟩ := Subgroup.mem_sup.mp hb
    obtain ⟨α, hα, rfl⟩ := hp
    obtain ⟨γ, hγ, hγθ⟩ := (mem_spinorNormGroup Q hQ).mp hα
    have hγθ' : spinorNorm Q F γ = sqClassOf (α : F) := by
      rw [hγθ, sqClassOf_of_ne_zero α.ne_zero, Units.mk0_val]
    have hθγ : ∀ v : HeightOneSpectrum (𝓞 F), spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ) =
        sqClassOf (algebraMap F (v.adicCompletion F) (α : F)) := fun v =>
      spinorNorm_orthMap_of hQ v γ α.ne_zero hγθ'
    set b' : OAf Q := (diagF Q γ)⁻¹ * (b : OAf Q) with hb'
    have hb'v : ∀ v, b' v = (orthMap Q _ γ)⁻¹ * (b : OAf Q) v := fun v => rfl
    have hb'rot : ∀ v, b' v ∈ Tamagawa.soSub Q (v.adicCompletion F) := fun v => by
      rw [hb'v]
      exact (Tamagawa.soSub Q _).mul_mem ((Tamagawa.soSub Q _).inv_mem (orthMap_mem_soSub (Q := Q) (v.adicCompletion F) hγ)) (b.2 v)
    have hT : ∀ v, spinorNorm Q (v.adicCompletion F) (b' v) ∈ localSpinorNormSq Q hQ v L := by
      intro v
      have h1 := hx v
      have hj' := (mem_spinorIdeles Q hQ).mp hj v
      rw [hb'v, ← spinorNormHom_apply Q _ hQ, map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hθγ,
        SqClass.inv_eq]
      rw [ideleAt_mul, sqClassOf_mul (ideleAt_ne_zero _ v) (ideleAt_ne_zero j v), ideleAt_unitEmbedding] at h1
      have := Subgroup.mul_mem _ h1 hj'
      convert this using 1
      set a := sqClassOf (algebraMap F (v.adicCompletion F) (α : F))
      set s := sqClassOf (ideleAt j v)
      set t := spinorNorm Q (v.adicCompletion F) ((b : OAf Q) v)
      calc a * t = a * t * (s * s) := by rw [SqClass.mul_self, mul_one]
        _ = a * s * t * s := by ac_rfl
    have hρ : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ρ ∈ locStabV Q v L ⊓ Tamagawa.soSub Q (v.adicCompletion F),
        spinorNorm Q (v.adicCompletion F) ρ = spinorNorm Q (v.adicCompletion F) (b' v) ∧
          (b' v ∈ locStabV Q v L → ρ = b' v) := by
      intro v
      by_cases hv : b' v ∈ locStabV Q v L
      · exact ⟨b' v, ⟨hv, hb'rot v⟩, rfl, fun _ => rfl⟩
      · obtain ⟨ρ, hρ, hρθ⟩ := (mem_localSpinorNormSq Q hQ).mp (hT v)
        exact ⟨ρ, hρ, hρθ, fun h => absurd h hv⟩
    choose ρ hρ hρθ hρeq using hρ
    let ρA : OAf Q := ⟨ρ, by
      filter_upwards [b'.2, loc_eventually_std L.2] with v h1 h2
      have hv : b' v ∈ locStabV Q v L := (locStabV_eq_stdStab Q v L h2).mpr h1
      rw [hρeq v hv]; exact h1⟩
    have hρL : ρA ∈ locStab Q L := fun v => (Subgroup.mem_inf.mp (hρ v)).1
    set κ : OAf Q := b' * ρA⁻¹ with hκdef
    have hκ : κ ∈ spinorKernelAf Q := by
      intro v
      have e : κ v = b' v * (ρ v)⁻¹ := rfl
      rw [e, spinorKernel_eq_ker Q _ hQ, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul, map_inv,
        spinorNormHom_apply, spinorNormHom_apply, hρθ, mul_inv_cancel]
      refine ⟨rfl, ?_⟩
      have h1 : detHom Q _ (b' v) = 1 := Units.ext (by rw [detHom_val, Units.val_one]; exact hb'rot v)
      have h2 : detHom Q _ (ρ v) = 1 :=
        Units.ext (by rw [detHom_val, Units.val_one]; exact (Subgroup.mem_inf.mp (hρ v)).2)
      rw [map_mul, map_inv, h1, h2, inv_one, mul_one]
    have hbe : (b : OAf Q) = diagF Q γ * κ * ρA := by
      rw [hκdef, hb']; group
    rw [hbe]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((mem_spnPlusGroup Q).mpr ⟨γ, hγ, κ, hκ, rfl⟩))
      (Subgroup.mem_sup_right hρL)
  · intro hb
    have := spnPlusGroup_normal Q hQ
    rw [spnPlusLocGroup, ← SetLike.mem_coe, Subgroup.normal_mul] at hb
    obtain ⟨g, hg, s, hs, hgs⟩ := hb
    obtain ⟨γ, hγ, k, hk, rfl⟩ := (mem_spnPlusGroup Q).mp hg
    obtain ⟨xs, hxs, hxe⟩ := exists_symmProd_eq Q F hQ γ
    set c := valProd Q F xs
    have hc : c ≠ 0 := valProd_ne_zero Q F hxs
    have hγθ : spinorNorm Q F γ = sqClassOf c := by rw [← hxe, spinorNorm_symmProd Q F hQ xs hxs]
    have hαD : Units.mk0 c hc ∈ spinorNormGroup Q hQ :=
      (mem_spinorNormGroup Q hQ).mpr ⟨γ, hγ, by rw [hγθ, sqClassOf_of_ne_zero hc]⟩
    have hassoc : SpinorIdeleAssoc Q hQ L b (IdeleGroup.unitEmbedding (𝓞 F) F (Units.mk0 c hc)) := by
      intro v
      have hsv : s v ∈ Tamagawa.soSub Q (v.adicCompletion F) := by
        have e : s v = (orthMap Q _ γ * k v)⁻¹ * (b : OAf Q) v := by
          rw [← hgs]; change s v = (orthMap Q _ γ * k v)⁻¹ * (orthMap Q _ γ * k v * s v); group
        rw [e]
        exact (Tamagawa.soSub Q _).mul_mem ((Tamagawa.soSub Q _).inv_mem ((Tamagawa.soSub Q _).mul_mem
          (orthMap_mem_soSub (Q := Q) (v.adicCompletion F) hγ) (spinorKernel_le_soSub' hQ _ (hk v)))) (b.2 v)
      have e : (b : OAf Q) v = orthMap Q _ γ * k v * s v := by rw [← hgs]; rfl
      have hk1 : spinorNorm Q (v.adicCompletion F) (k v) = 1 := by
        have := hk v
        rw [spinorKernel_eq_ker Q _ hQ, Subgroup.mem_inf, MonoidHom.mem_ker, spinorNormHom_apply] at this
        exact this.1
      rw [ideleAt_unitEmbedding, Units.val_mk0, e, ← spinorNormHom_apply Q _ hQ, map_mul, map_mul,
        spinorNormHom_apply, spinorNormHom_apply, spinorNormHom_apply, spinorNorm_orthMap_of hQ v γ hc hγθ,
        hk1, mul_one, ← mul_assoc, SqClass.mul_self, one_mul]
      exact (mem_localSpinorNormSq Q hQ).mpr ⟨s v, ⟨hs v, hsv⟩, rfl⟩
    rw [spinorIdeleMap_eq hassoc, ← QuotientGroup.mk_one, QuotientGroup.eq, mul_one, inv_mem_iff]
    exact Subgroup.mem_sup_left ⟨_, hαD, rfl⟩

/-- **$\Phi$ is surjective for $n \ge 3$** (O'Meara 1973, §102B, proof of 102:7, step 4, p. 301): given an idèle $i$,
take $\Sigma_\mathfrak p = 1$ where $i_\mathfrak p \in \theta(O^+(L_\mathfrak p))$ (all but finitely many $\mathfrak p$, by
92:5 at the good spots, `spinorNormsContainUnits_of_goodSpot`), and a rotation with spinor norm $i_\mathfrak p$ elsewhere
($\theta(O^+(V_\mathfrak p)) = F_\mathfrak p^\times$ for $n \ge 3$, 91:6). -/
@[kb "omeara1963" "§102B, proof of 102:7, step 4, p. 301 (Φ is surjective, n ≥ 3)"]
theorem spinorIdeleMap_surjective (hn : 3 ≤ n) (L : Lat F n) : Function.Surjective (spinorIdeleMap Q hQ L) := by
  classical
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    have hg : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g ∈ Tamagawa.soSub Q (v.adicCompletion F),
        (sqClassOf (ideleAt x v) ∈ localSpinorNormSq Q hQ v L → g = 1) ∧
        (sqClassOf (ideleAt x v) ∉ localSpinorNormSq Q hQ v L →
          spinorNorm Q (v.adicCompletion F) g = sqClassOf (ideleAt x v)) := by
      intro v
      by_cases hv : sqClassOf (ideleAt x v) ∈ localSpinorNormSq Q hQ v L
      · exact ⟨1, (Tamagawa.soSub Q _).one_mem, fun _ => rfl, fun h => absurd hv h⟩
      · obtain ⟨g, hg, hgσ⟩ :=
          Hanke2005.SpinorIdele.exists_so_spinorNorm_local Q v hQ hn (ideleAt_ne_zero x v)
        exact ⟨g, hg, fun h => absurd h hv, fun _ => hgσ⟩
    choose g hgso hg1 hgσ using hg
    have hev : ∀ᶠ v in Filter.cofinite, sqClassOf (ideleAt x v) ∈ localSpinorNormSq Q hQ v L := by
      have hunit := (NumberField.AdeleRing.isUnit_iff.mp (Units.isUnit x)).2.2
      filter_upwards [hunit, eventually_goodSpot Q hQ L] with v hu hv
      obtain ⟨g, hg, hd, hθ⟩ := spinorNormsContainUnits_of_goodSpot Q v hQ (by omega) L hv (ideleAt x v) hu
      refine (mem_localSpinorNormSq Q hQ).mpr ⟨g, ⟨hg, ?_⟩, hθ⟩
      change g ∈ Tamagawa.soSub Q _
      rw [Tamagawa.mem_soSub, ← detHom_val, hd, Units.val_one]
    let b : OAf Q := ⟨g, by
      filter_upwards [hev] with v hv
      rw [hg1 v hv]; exact (stdStab Q v).one_mem⟩
    refine ⟨⟨b, fun v => hgso v⟩, ?_⟩
    rw [spinorIdeleMap_eq (x := x)]
    intro v
    change sqClassOf (ideleAt x v) * spinorNorm Q _ (g v) ∈ _
    by_cases hv : sqClassOf (ideleAt x v) ∈ localSpinorNormSq Q hQ v L
    · rw [hg1 v hv, spinorNorm_one' Q hQ, mul_one]; exact hv
    · rw [hgσ v hv, SqClass.mul_self]; exact Subgroup.one_mem _

end KernelImage

/-! ### 102:7, 102:7a, 102:8a -/

section Main

variable {Q}

/-- **O'Meara, Theorem 102:7** (O'Meara 1973, §102B, p. 300): for a lattice $L$ on a regular quadratic space
$V = (F^n, Q)$ (`hQ`) over a number field $F$ with $n \ge 3$, the number $g^+(L)$ of proper spinor genera in
$\operatorname{gen}L$ (`properSpinorGenusNumber`) is the index $(J_F : P_DJ_F^L)$ of
$P_DJ_F^L$ = `principalSpinorIdelesSup Q hQ L` in the idèle group $J_F$ = `IdeleGroup (𝓞 F) F`, where
$D = \theta(O^+(V))$, $P_D$ = the principal idèles $(\alpha)$, $\alpha \in D$, and $J_F^L$ = the idèles $i$ with
$i_\mathfrak p \in \theta(O^+(L_\mathfrak p))$ at every finite spot $\mathfrak p$ (`spinorIdeles`). $S$ is the set of
all finite spots. Unconditional. -/
@[kb "omeara1963" "§102B, 102:7, p. 300"]
theorem omeara102_7 (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (L : Lat F n) :
    properSpinorGenusNumber Q L = (principalSpinorIdelesSup Q hQ L).index := by
  rw [properSpinorGenusNumber_eq_index_soAf Q hQ L, ← ker_spinorIdeleMap hQ L, Subgroup.index, Subgroup.index]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (spinorIdeleMap_surjective hQ hn L)).toEquiv

/-- **O'Meara, Corollary 102:7a** (O'Meara 1973, §102B, p. 302): for a lattice $L$ on a regular quadratic space
$V = (F^n, Q)$ over a number field, of any dimension $n$: $g^+(L) = (J_V : J'_VP_VJ_L)$, where $J_V$ =
`Tamagawa.soAf Q` is the group of rotation idèles and $J'_VP_VJ_L$ is `spnPlusLocGroup Q L` (intersected with
$J_V$), and $g^+(L)$ divides $(J_F : P_DJ_F^L)$. Unconditional. -/
@[kb "omeara1963" "§102B, 102:7a, p. 302"]
theorem omeara102_7a (hQ : Q.Nondegenerate) (L : Lat F n) :
    properSpinorGenusNumber Q L = ((spnPlusLocGroup Q L).subgroupOf (Tamagawa.soAf Q)).index ∧
      properSpinorGenusNumber Q L ∣ (principalSpinorIdelesSup Q hQ L).index := by
  refine ⟨properSpinorGenusNumber_eq_index_soAf Q hQ L, ?_⟩
  rw [properSpinorGenusNumber_eq_index_soAf Q hQ L, ← ker_spinorIdeleMap hQ L, Subgroup.index, Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

/-- **O'Meara, Corollary 102:8a** (O'Meara 1973, §102B, p. 304; for $n \ge 3$ the first assertion of Theorem 102:8,
p. 302): for a lattice $L$ on a regular quadratic space $V = (F^n, Q)$ over a number field, of any dimension $n$, the
number $g^+(L)$ of proper spinor genera in $\operatorname{gen}L$ is a power of $2$. *Proof:* $g^+(L)$ is the order of
the finite group $O(V)(\mathbb A_f)/P_VJ'_VO(\hat L)$ (`properSpinorGenusNumber_eq_index`,
`genusProperSpinorGenera_finite`), whose elements square to $1$ (squares lie in $J'_V$). Unconditional. -/
@[kb "omeara1963" "§102B, 102:8a, p. 304; 102:8, p. 302 (g⁺(L) = 2^r)"]
theorem omeara102_8a (hQ : Q.Nondegenerate) (L : Lat F n) : ∃ r : ℕ, properSpinorGenusNumber Q L = 2 ^ r := by
  rw [properSpinorGenusNumber_eq_index Q hQ L]
  have := spnPlusLocGroup_normal Q hQ L
  have : Finite (genusProperSpinorGenera Q L) := (genusProperSpinorGenera_finite Q hQ L).to_subtype
  have : Finite (OAf Q ⧸ spnPlusLocGroup Q L) := Finite.of_equiv _ (genusProperSpinorGeneraEquiv Q hQ L)
  have hp : IsPGroup 2 (OAf Q ⧸ spnPlusLocGroup Q L) := by
    intro x
    refine ⟨1, ?_⟩
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (sq_mem_spinorKernelAf Q hQ g))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  exact ⟨k, by rw [Subgroup.index, hk]⟩

/-- **The idèle index of 102:7 is a power of $2$** (O'Meara 1973, §102B, 102:8, p. 302, first assertion, in the form
$(J_F : P_DJ_F^L) = 2^r$): for $n \ge 3$. From 102:7 and 102:8a. Unconditional. -/
@[kb "omeara1963" "§102B, 102:8, p. 302 (the number of proper spinor genera is 2^r)"]
theorem omeara102_8_index (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (L : Lat F n) :
    ∃ r : ℕ, (principalSpinorIdelesSup Q hQ L).index = 2 ^ r := by
  rw [← omeara102_7 hQ hn L]; exact omeara102_8a hQ L

end Main

end QuadFormsKB.Lattices
