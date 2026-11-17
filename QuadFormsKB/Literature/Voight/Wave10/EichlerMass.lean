/-
# The Eichler mass formula for Eichler orders, from Proposition 26.6.4 (Voight, Theorem 26.1.12)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Proposition 26.6.4 (p. 445),
Lemma 26.6.7 (p. 446), Theorem 26.1.12 (p. 433), Theorem 25.3.18 (p. 423).

**Setting.** $F$ a totally real number field with ring of integers $R = \mathbb Z_F$, $B = (a,b)_F$ = `QuatF F a b`
totally definite, $\mathcal O \subseteq B$ an Eichler order of level $\mathfrak M$ with a $\mathbb Z_F$-basis
(`IsEichlerOrderOfLevel`), $\operatorname{mass}(\operatorname{Cls}\mathcal O)$ = `clsMass O`. For a prime $\mathfrak p$ write
$q = N\mathfrak p$ and $e_{\mathfrak p} = \operatorname{ord}_{\mathfrak p}\mathfrak M$.

**Theorem** (`eichlerMassFormulaEichlerOrders_of`): the Eichler mass formula for Eichler orders
(`Voight.EichlerMassFormulaEichlerOrders F`, Theorem 26.1.12) follows from two smaller named inputs,
* `Wave6.MassSuperorder F` (Proposition 26.6.4: the mass of a suborder differing at one prime is the local unit index
  times the mass of the superorder), and
* `Voight.EichlerMassFormulaMaximal F` (Theorem 26.1.12 for maximal orders, every maximal order).
Over $\mathbb Q$ (`eichlerMassFormulaEichlerOrdersRat_of`, Theorem 25.3.18) the same two inputs for $F = \mathbb Q$ suffice.

*Proof* (Voight, proof of Theorem 26.1.12, with the steps made explicit). By 23.4.19 (`Wave9.eichlerLocalLevel`) at every
prime $\mathfrak p \mid \mathfrak M$ there is $\varphi_{\mathfrak p} : B_{\mathfrak p} \cong \mathrm M_2(F_{\mathfrak p})$ with
$\varphi_{\mathfrak p}(\mathcal O_{\mathfrak p}) = \mathcal O_0(\pi^{e_{\mathfrak p}})$. For a set $T$ of primes dividing $\mathfrak M$ glue
(`Wave9.exists_order_localOrder_eq`) the order $\mathcal O_T$ whose completion is $\varphi_{\mathfrak p}^{-1}(\mathrm M_2(R_{\mathfrak p}))$ at
$\mathfrak p \in T$ and $\mathcal O_{\mathfrak p}$ elsewhere. Adding one prime $\mathfrak p$ to $T$ changes the order at $\mathfrak p$ only, and the
local unit index is $[\mathrm{GL}_2(R_{\mathfrak p}) : \mathcal O_0(\pi^e)^\times] = q^{e-1}(q+1)$ (`Wave4.index_units_stdEichlerOrder`,
Lemma 26.6.7). So by Proposition 26.6.4 and induction,
$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \prod_{\mathfrak p \mid \mathfrak M} q^{e_{\mathfrak p}-1}(q+1)\cdot
\operatorname{mass}(\operatorname{Cls}\mathcal O_{T})$ with $T$ all primes dividing $\mathfrak M$. Then $\mathcal O_T$ is maximal (every
completion is), and $\prod_{\mathfrak p \mid \mathfrak M} q^{e_{\mathfrak p}-1}(q+1) = N\mathfrak M\prod_{\mathfrak p \mid \mathfrak M}(1 + 1/q) =
\psi(\mathfrak M)$.

The order $\mathcal O_T$ for $T$ all primes dividing $\mathfrak M$ is the maximal order $\mathcal O_1$ of $\mathcal O = \mathcal O_1 \cap \mathcal O_2$
in the book; it need not have a $\mathbb Z_F$-basis, which is why the maximal-order input is used for every maximal order.
-/
import QuadFormsKB.Literature.Voight.Wave9.EichlerLevel
import QuadFormsKB.Literature.Voight.Wave4.ClassSet
import QuadFormsKB.Literature.Voight.Wave5.MassGeneral
import QuadFormsKB.Literature.Voight.Wave4.EichlerIndex
import QuadFormsKB.LocalDensity.NFBridge

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Quaternion

noncomputable section

namespace QuadFormsKB.Voight.Wave10

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Voight QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4
  QuadFormsKB.Voight.Wave9 QuadFormsKB.Voight.MassWave2 QuadFormsKB.NFEuler

/-! ### Unit indices of nested subalgebras -/

section UnitIdx

variable {R X Y : Type*} [CommRing R] [Ring X] [Algebra R X] [Ring Y] [Algebra R Y]

/-- The index $[B^\times : A^\times]$ of the unit group of a subalgebra $A \subseteq B$ (embedded by inclusion) in the unit
group of $B$ (`Subgroup.index`, $0$ if infinite). -/
def unitIdx {A B : Subalgebra R X} (h : A ≤ B) : ℕ :=
  (Units.map (Subalgebra.inclusion h).toMonoidHom).range.index

/-- The unit index depends only on the two subalgebras. -/
theorem unitIdx_congr {A B A' B' : Subalgebra R X} (h : A ≤ B) (h' : A' ≤ B') (hA : A = A') (hB : B = B') :
    unitIdx h = unitIdx h' := by
  subst hA; subst hB; rfl

/-- The unit index is invariant under an algebra isomorphism $\psi : X \cong Y$:
$[\psi(B)^\times : \psi(A)^\times] = [B^\times : A^\times]$. -/
theorem unitIdx_map (ψ : X ≃ₐ[R] Y) {A B : Subalgebra R X} (h : A ≤ B) :
    unitIdx (Subalgebra.map_mono h : A.map (ψ : X →ₐ[R] Y) ≤ B.map (ψ : X →ₐ[R] Y)) = unitIdx h := by
  let eA : A ≃ₐ[R] A.map (ψ : X →ₐ[R] Y) := Subalgebra.equivMapOfInjective A (ψ : X →ₐ[R] Y) ψ.injective
  let eB : B ≃ₐ[R] B.map (ψ : X →ₐ[R] Y) := Subalgebra.equivMapOfInjective B (ψ : X →ₐ[R] Y) ψ.injective
  let EA : Aˣ ≃* (A.map (ψ : X →ₐ[R] Y))ˣ := Units.mapEquiv eA.toMulEquiv
  let EB : Bˣ ≃* (B.map (ψ : X →ₐ[R] Y))ˣ := Units.mapEquiv eB.toMulEquiv
  have hcomm : (Units.map (Subalgebra.inclusion (Subalgebra.map_mono h)).toMonoidHom).comp EA.toMonoidHom =
      EB.toMonoidHom.comp (Units.map (Subalgebra.inclusion h).toMonoidHom) := by
    ext u
    rfl
  have hrange : (Units.map (Subalgebra.inclusion (Subalgebra.map_mono h)).toMonoidHom).range =
      (Units.map (Subalgebra.inclusion h).toMonoidHom).range.map EB.toMonoidHom := by
    rw [← MonoidHom.range_comp, ← hcomm, MonoidHom.range_comp]
    rw [show EA.toMonoidHom.range = ⊤ from MonoidHom.range_eq_top.2 EA.surjective, ← MonoidHom.range_eq_map]
  unfold unitIdx
  rw [hrange]
  exact Subgroup.index_map_equiv _ EB

end UnitIdx

/-! ### Local facts at a split prime -/

section Local

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The maximal order $\varphi^{-1}(\mathrm M_2(R_v))$ of $B_v$ for an isomorphism $\varphi : B_v \cong \mathrm M_2(F_v)$. -/
def maxAt (φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv) : Subalgebra 𝔬 (QuatV v a b) :=
  (matOrder 𝔬 Fv).map ((φ.symm : Matrix (Fin 2) (Fin 2) Fv →ₐ[Fv] QuatV v a b).restrictScalars 𝔬)

theorem maxAt_isMaximalOrder (φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv) :
    IsMaximalOrder 𝔬 Fv (maxAt v φ) :=
  isMaximalOrder_matOrder.map φ.symm

/-- $\varphi(\varphi^{-1}(\mathrm M_2(R_v))) = \mathrm M_2(R_v)$. -/
theorem map_maxAt (φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv) :
    (maxAt v φ).map ((φ : QuatV v a b →ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv).restrictScalars 𝔬) = matOrder 𝔬 Fv := by
  rw [maxAt, Subalgebra.map_map]
  conv_rhs => rw [← Subalgebra.map_id (matOrder 𝔬 Fv)]
  congr 1
  exact AlgHom.ext fun x => φ.apply_symm_apply x

/-- An order of $B_v$ carried onto a subalgebra $\Lambda'$ by $\varphi$ is $\varphi^{-1}(\Lambda')$. -/
theorem eq_map_symm_of_map_eq {Λ : Subalgebra 𝔬 (QuatV v a b)} {Λ' : Subalgebra 𝔬 (Matrix (Fin 2) (Fin 2) Fv)}
    (φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv)
    (h : Λ.map ((φ : QuatV v a b →ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv).restrictScalars 𝔬) = Λ') :
    Λ = Λ'.map ((φ.symm : Matrix (Fin 2) (Fin 2) Fv →ₐ[Fv] QuatV v a b).restrictScalars 𝔬) := by
  rw [← h, Subalgebra.map_map]
  conv_lhs => rw [← Subalgebra.map_id Λ]
  congr 1
  exact AlgHom.ext fun x => (φ.symm_apply_apply x).symm

/-- If $\varphi(\Lambda) = \mathcal O_0(\pi^e)$ then $\Lambda \subseteq \varphi^{-1}(\mathrm M_2(R_v))$. -/
theorem le_maxAt {Λ : Subalgebra 𝔬 (QuatV v a b)} (φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv) (e : ℕ)
    (h : Λ.map ((φ : QuatV v a b →ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv).restrictScalars 𝔬) =
      stdEichlerOrder 𝔬 Fv (LocalDensity.NF.π v) e) :
    Λ ≤ maxAt v φ := by
  rw [eq_map_symm_of_map_eq v φ h]
  exact Subalgebra.map_mono (stdEichlerOrder_le_matOrder _ e)

/-- **The local unit index** (Voight 2021, Lemma 26.6.7): if $\varphi(\Lambda) = \mathcal O_0(\pi^e)$ with $e \ge 1$, then
$[\varphi^{-1}(\mathrm M_2(R_v))^\times : \Lambda^\times] = q^{e-1}(q+1)$, $q = N v$. -/
@[kb "voight2021" "Lemma 26.6.7, p. 446"]
theorem unitIdx_maxAt {Λ : Subalgebra 𝔬 (QuatV v a b)} (φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv) {e : ℕ}
    (he : 1 ≤ e)
    (h : Λ.map ((φ : QuatV v a b →ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv).restrictScalars 𝔬) =
      stdEichlerOrder 𝔬 Fv (LocalDensity.NF.π v) e) :
    unitIdx (le_maxAt v φ e h) = Ideal.absNorm v.asIdeal ^ (e - 1) * (Ideal.absNorm v.asIdeal + 1) := by
  let ψ : QuatV v a b ≃ₐ[𝔬] Matrix (Fin 2) (Fin 2) Fv := φ.restrictScalars 𝔬
  have hψ : (ψ : QuatV v a b →ₐ[𝔬] Matrix (Fin 2) (Fin 2) Fv) =
      (φ : QuatV v a b →ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv).restrictScalars 𝔬 := rfl
  rw [← unitIdx_map ψ (le_maxAt v φ e h)]
  rw [unitIdx_congr _ (stdEichlerOrder_le_matOrder (K := Fv) (LocalDensity.NF.π v) e)
    (by rw [hψ, h]) (by rw [hψ, map_maxAt])]
  rw [← LocalDensity.NF.q_completion v]
  exact index_units_stdEichlerOrder (LocalDensity.NF.irreducible_π v) he

end Local

/-! ### The primes dividing the level -/

section Level

variable {F : Type} [Field F] [NumberField F]

/-- The exponent $e_v = \operatorname{ord}_v\mathfrak M$ of a prime $v$ in $\mathfrak M$ (multiplicity among the normalized factors). -/
abbrev ordAt (𝔐 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors 𝔐).count v.asIdeal

theorem finite_levelPrimes (𝔐 : Ideal (𝓞 F)) : {v : HeightOneSpectrum (𝓞 F) | 0 < ordAt 𝔐 v}.Finite := by
  classical
  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
    fun v w h => HeightOneSpectrum.ext h
  refine ((UniqueFactorizationMonoid.normalizedFactors 𝔐).toFinset.finite_toSet.preimage hinj.injOn).subset ?_
  intro v hv
  have hv' : 0 < ordAt 𝔐 v := hv
  rw [Multiset.count_pos] at hv'
  exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 hv')

/-- The finite set of primes $v \mid \mathfrak M$. -/
def levelPrimes (𝔐 : Ideal (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 F)) := (finite_levelPrimes 𝔐).toFinset

theorem mem_levelPrimes {𝔐 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} : v ∈ levelPrimes 𝔐 ↔ 0 < ordAt 𝔐 v := by
  simp [levelPrimes]

/-- $\prod_{v \mid \mathfrak M} q_v^{e_v - 1}(q_v + 1) = \psi(\mathfrak M) = N\mathfrak M\prod_{v \mid \mathfrak M}(1 + q_v^{-1})$. -/
theorem prod_levelPrimes {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) :
    ∏ v ∈ levelPrimes 𝔐, ((Ideal.absNorm v.asIdeal : ℝ) ^ (ordAt 𝔐 v - 1) * ((Ideal.absNorm v.asIdeal : ℝ) + 1)) =
      dedekindPsi 𝔐 := by
  classical
  set s := UniqueFactorizationMonoid.normalizedFactors 𝔐 with hs
  have hN : (Ideal.absNorm 𝔐 : ℝ) = ∏ p ∈ s.toFinset, (Ideal.absNorm p : ℝ) ^ s.count p := by
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self h𝔐]
    rw [map_multiset_prod, ← hs, Finset.prod_multiset_map_count]
    push_cast
    rfl
  rw [dedekindPsi, hN, ← hs, ← Finset.prod_mul_distrib]
  refine Finset.prod_nbij (fun v => v.asIdeal) ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_levelPrimes, Multiset.count_pos] at hv
    exact Multiset.mem_toFinset.2 hv
  · intro v _ w _ h
    exact HeightOneSpectrum.ext h
  · intro p hp
    rw [Finset.mem_coe, Multiset.mem_toFinset] at hp
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor p hp
    refine ⟨⟨p, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩, ?_, rfl⟩
    rw [Finset.mem_coe, mem_levelPrimes, Multiset.count_pos]
    exact hp
  · intro v hv
    have hc := mem_levelPrimes.1 hv
    have hN0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
    obtain ⟨c, hc'⟩ : ∃ c, ordAt 𝔐 v = c + 1 := ⟨ordAt 𝔐 v - 1, by omega⟩
    change _ = (Ideal.absNorm v.asIdeal : ℝ) ^ ordAt 𝔐 v * (1 + (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
    rw [hc', Nat.add_sub_cancel, pow_succ]
    field_simp

/-- A prime dividing an ideal $\mathfrak M$ coprime to $\mathfrak D$ is not ramified. -/
theorem not_mem_ramFin_of_mem_levelPrimes {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) {𝔐 : Ideal (𝓞 F)}
    (hcop : IsCoprime 𝔐 (∏ w ∈ ramFin ha hb, w.asIdeal)) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ levelPrimes 𝔐) :
    v ∉ ramFin ha hb := by
  intro hr
  have h1 : v.asIdeal ∣ 𝔐 := by
    have := mem_levelPrimes.1 hv
    rw [Multiset.count_pos] at this
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors this
  have h2 : v.asIdeal ∣ ∏ w ∈ ramFin ha hb, w.asIdeal := Finset.dvd_prod_of_mem _ hr
  have hu := hcop.isUnit_of_dvd' h1 h2
  rw [Ideal.isUnit_iff] at hu
  exact v.isPrime.ne_top hu

/-- The reduced discriminant of an order with a $\mathbb Z_F$-basis is nonzero. -/
theorem ne_bot_of_hasDiscrd {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) {𝔑 : Ideal (𝓞 F)} (h : HasDiscrd O 𝔑) :
    𝔑 ≠ ⊥ := by
  intro h𝔑
  obtain ⟨d, hd, hspan⟩ := h e
  rw [h𝔑, ← Ideal.zero_eq_bot, zero_pow two_ne_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hspan
  have hO : IsOrder (𝓞 F) F O := isOrder_of_basis e
  have : Submodule.IsLattice F (Subalgebra.toSubmodule O) := ⟨hO.fg, hO.span⟩
  set fb : Module.Basis (Fin 4) F (QuatF F a b) := e.extendOfIsLattice F
  have h2ab : (2 : F) * algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha))
      ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hb)
  apply Disc.gramTrd_ne_zero h2ab fb
  have hfb : (fun q => fb q) = fun q => (e q : QuatF F a b) := by
    funext q; exact Module.Basis.extendOfIsLattice_apply F e q
  rw [hfb, Disc.gramTrd, ← trdGramDet, ← hd, hspan, map_zero]

end Level

/-! ### Reduction to a maximal order -/

section Core

variable {F : Type} [Field F] [NumberField F]

/-- **Reduction of the mass of an Eichler order to a maximal order** (Voight 2021, proof of Theorem 26.1.12): assuming
Proposition 26.6.4 (`Wave6.MassSuperorder F`), for an Eichler order $\mathcal O$ of level $\mathfrak M$ with a $\mathbb Z_F$-basis in a
totally definite $B = (a,b)_F$ over a totally real number field $F$ there is a maximal order $\mathcal O_1 \supseteq \mathcal O$
with $\operatorname{mass}(\operatorname{Cls}\mathcal O) = \psi(\mathfrak M)\operatorname{mass}(\operatorname{Cls}\mathcal O_1)$. -/
@[kb "voight2021" "Theorem 26.1.12, p. 433; Proposition 26.6.4, p. 445"]
theorem exists_maximal_clsMass_eq [IsTotallyReal F] (H : Wave6.MassSuperorder F) {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hdef : IsTotDefinite a b) {O : Subalgebra (𝓞 F) (QuatF F a b)} {𝔐 : Ideal (𝓞 F)}
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) (hlev : IsEichlerOrderOfLevel ha hb O 𝔐) :
    ∃ O₁ : Subalgebra (𝓞 F) (QuatF F a b), IsMaximalOrder (𝓞 F) F O₁ ∧ clsMass O = dedekindPsi 𝔐 * classMass O₁ := by
  classical
  have hO : IsOrder (𝓞 F) F O := isOrder_of_basis e
  have hloc := eichlerLocalLevel F a b ha hb O 𝔐 ⟨e⟩ hlev
  obtain ⟨-, hcop, hdisc⟩ := hlev
  have h𝔐 : 𝔐 ≠ ⊥ := fun h => ne_bot_of_hasDiscrd ha hb e hdisc (by rw [h, Ideal.mul_bot])
  -- the split isomorphisms at the primes dividing the level
  have hφ : ∀ v ∈ levelPrimes 𝔐, ∃ φ : QuatV v a b ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F),
      (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[v.adicCompletion F] _).restrictScalars
        (v.adicCompletionIntegers F)) =
        stdEichlerOrder (v.adicCompletionIntegers F) (v.adicCompletion F) (LocalDensity.NF.π v)
          ((UniqueFactorizationMonoid.normalizedFactors 𝔐).count v.asIdeal) :=
    fun v hv => (hloc v).2 (not_mem_ramFin_of_mem_levelPrimes ha hb hcop hv)
  choose φ hφ using hφ
  -- the glued local families: maximal at the primes of `T` dividing the level, `O_v` elsewhere
  let G : Finset (HeightOneSpectrum (𝓞 F)) →
      ∀ v : HeightOneSpectrum (𝓞 F), Subalgebra (v.adicCompletionIntegers F) (QuatV v a b) :=
    fun T v => if hv : v ∈ levelPrimes 𝔐 ∧ v ∈ T then maxAt v (φ v hv.1) else localOrder (v := v) a b O
  have hG : ∀ T v, IsOrder (v.adicCompletionIntegers F) (v.adicCompletion F) (G T v) := by
    intro T v
    simp only [G]
    split_ifs with hv
    · exact (maxAt_isMaximalOrder v _).1
    · exact Gen.isOrder_localOrder_gen v hO
  have hex : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), ∃ O' : Subalgebra (𝓞 F) (QuatF F a b),
      IsOrder (𝓞 F) F O' ∧ ∀ v, localOrder (v := v) a b O' = G T v := by
    intro T
    refine exists_order_localOrder_eq hO (G T) (hG T) ?_
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
    simp only [G]
    rw [dif_neg]
    exact fun h => hv h.2
  have hGins : ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (w v : HeightOneSpectrum (𝓞 F)), v ≠ w →
      G T v = G (insert w T) v := by
    intro T w v hvw
    simp only [G]
    by_cases h : v ∈ levelPrimes 𝔐 ∧ v ∈ T
    · rw [dif_pos h, dif_pos ⟨h.1, Finset.mem_insert_of_mem h.2⟩]
    · rw [dif_neg h, dif_neg]
      rintro ⟨h1, h2⟩
      exact h ⟨h1, (Finset.mem_insert.1 h2).resolve_left hvw⟩
  -- induction over the primes dividing the level
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), T ⊆ levelPrimes 𝔐 →
      ∀ O' : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O' → (∀ v, localOrder (v := v) a b O' = G T v) →
      clsMass O = (∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℝ) ^ (ordAt 𝔐 v - 1) *
        ((Ideal.absNorm v.asIdeal : ℝ) + 1))) * clsMass O' := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ O' hO' hloc'
      have : O = O' := order_eq_of_localOrder_eq hO hO' fun v => by
        rw [hloc' v]
        simp only [G]
        rw [dif_neg]
        exact fun h => Finset.notMem_empty v h.2
      rw [this, Finset.prod_empty, one_mul]
    | insert w T hw ih =>
      intro hsub O' hO' hloc'
      have hwL : w ∈ levelPrimes 𝔐 := hsub (Finset.mem_insert_self w T)
      have hTL : T ⊆ levelPrimes 𝔐 := (Finset.subset_insert w T).trans hsub
      obtain ⟨O₀, hO₀, hloc₀⟩ := hex T
      have hw₀ : localOrder (v := w) a b O₀ = localOrder (v := w) a b O := by
        rw [hloc₀ w]
        simp only [G]
        rw [dif_neg]
        exact fun h => hw h.2
      have hw' : localOrder (v := w) a b O' = maxAt w (φ w hwL) := by
        rw [hloc' w]
        simp only [G]
        rw [dif_pos ⟨hwL, Finset.mem_insert_self w T⟩]
      have hagree : ∀ v, v ≠ w → localOrder (v := v) a b O₀ = localOrder (v := v) a b O' := by
        intro v hvw
        rw [hloc₀ v, hloc' v]
        exact hGins T w v hvw
      have hle : O₀ ≤ O' := order_le_of_localOrder_le hO' fun v => by
        by_cases hvw : v = w
        · subst hvw
          rw [hw₀, hw']
          exact le_maxAt v (φ v hwL) _ (hφ v hwL)
        · exact (hagree v hvw).le
      have hm := H inferInstance a b ha hb hdef O₀ O' hO₀ hO' hle w hagree
      have hidx : (Wave6.localUnitIndex w hle : ℝ) =
          (Ideal.absNorm w.asIdeal : ℝ) ^ (ordAt 𝔐 w - 1) * ((Ideal.absNorm w.asIdeal : ℝ) + 1) := by
        have h1 : Wave6.localUnitIndex w hle = unitIdx (Wave6.localOrder_mono w hle) := rfl
        rw [h1, unitIdx_congr _ (le_maxAt w (φ w hwL) _ (hφ w hwL)) hw₀ hw',
          unitIdx_maxAt w (φ w hwL) (mem_levelPrimes.1 hwL) (hφ w hwL)]
        push_cast
        ring
      rw [ih hTL O₀ hO₀ hloc₀, hm, hidx, Finset.prod_insert hw]
      ring
  obtain ⟨O₁, hO₁, hloc₁⟩ := hex (levelPrimes 𝔐)
  have hmass := key (levelPrimes 𝔐) le_rfl O₁ hO₁ hloc₁
  have hmax : IsMaximalOrder (𝓞 F) F O₁ := isMaximalOrder_of_forall_localOrder hO₁ fun v => by
    rw [hloc₁ v]
    simp only [G]
    split_ifs with hv
    · exact maxAt_isMaximalOrder v _
    · have hvL : v ∉ levelPrimes 𝔐 := fun h => hv ⟨h, h⟩
      by_cases hr : v ∈ ramFin ha hb
      · exact (hloc v).1 hr
      · obtain ⟨ψ, hψ⟩ := (hloc v).2 hr
        have h0 : (UniqueFactorizationMonoid.normalizedFactors 𝔐).count v.asIdeal = 0 := by
          by_contra h0
          exact hvL (mem_levelPrimes.2 (Nat.pos_of_ne_zero h0))
        rw [h0, Wave6.stdEichlerOrder_zero] at hψ
        rw [eq_map_symm_of_map_eq v ψ hψ]
        exact isMaximalOrder_matOrder.map ψ.symm
  exact ⟨O₁, hmax, by rw [hmass, clsMass_eq_classMass ha hb hdef hmax, prod_levelPrimes h𝔐]⟩

end Core

/-! ### The Eichler mass formula for Eichler orders -/

section Main

variable {F : Type} [Field F] [NumberField F]

/-- **The Eichler mass formula for Eichler orders from Proposition 26.6.4 and the maximal case** (Voight 2021,
Theorem 26.1.12): for a totally real number field $F$, the named propositions `Wave6.MassSuperorder F`
(Proposition 26.6.4) and `EichlerMassFormulaMaximal F` (the formula for every maximal order) imply
`EichlerMassFormulaEichlerOrders F`: for $B = (a,b)_F$ totally definite and an Eichler order $\mathcal O$ of level
$\mathfrak M$ with a $\mathbb Z_F$-basis,
$$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \frac{2\,\zeta_F(2)}{(2\pi)^{2n}}\,|d_F|^{3/2}\,h_F\,
\varphi(\mathfrak D)\,\psi(\mathfrak M).$$ -/
@[kb "voight2021" "Theorem 26.1.12, p. 433; Proposition 26.6.4, p. 445"]
theorem eichlerMassFormulaEichlerOrders_of [IsTotallyReal F] (H : Wave6.MassSuperorder F)
    (Hmax : EichlerMassFormulaMaximal F) : EichlerMassFormulaEichlerOrders F := by
  intro a b ha hb hdef O 𝔐 hfree hlev
  obtain ⟨e⟩ := hfree
  obtain ⟨O₁, hmax, h⟩ := exists_maximal_clsMass_eq H ha hb hdef e hlev
  rw [h, Hmax a b ha hb hdef O₁ hmax]
  ring

/-- An Eichler order over a number field whose ring of integers is a principal ideal domain is an order. -/
theorem isOrder_of_isEichlerOrder [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (h : IsEichlerOrder O) : IsOrder (𝓞 F) F O := by
  obtain ⟨O₁, O₂, h₁, h₂, rfl⟩ := h
  apply isOrder_of_isLattice_latOf
  have : latOf (Subalgebra.toSubmodule (O₁ ⊓ O₂)) =
      latOf (Subalgebra.toSubmodule O₁) ⊓ latOf (Subalgebra.toSubmodule O₂) := by
    rw [← latOf_inf]; rfl
  rw [this]
  have := isLattice_latOf h₁.1
  have := isLattice_latOf h₂.1
  infer_instance

/-- An order over a number field whose ring of integers is a principal ideal domain has a $\mathbb Z_F$-basis
(of $4$ elements). -/
theorem nonempty_basis_of_isOrder [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsOrder (𝓞 F) F O) : Nonempty (Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) := by
  have : Submodule.IsLattice F (Subalgebra.toSubmodule O) := ⟨hO.fg, hO.span⟩
  have hr : Module.finrank (𝓞 F) (Subalgebra.toSubmodule O) = 4 := by
    have := Submodule.IsLattice.rank' F (Subalgebra.toSubmodule O)
    rw [QuaternionAlgebra.rank_eq_four] at this
    exact Module.finrank_eq_of_rank_eq this
  exact ⟨Module.finBasisOfFinrankEq _ _ hr⟩

/-- **The Eichler mass formula for Eichler orders over $\mathbb Q$ from Proposition 26.6.4 and the maximal case**
(Voight 2021, Theorem 25.3.18): the named propositions `Wave6.MassSuperorder ℚ` (Proposition 26.6.4 over $\mathbb Q$) and
`EichlerMassFormulaRat` (Theorem 25.1.1, every maximal order) imply `EichlerMassFormulaEichlerOrdersRat`: for a definite
$B = (a,b)_{\mathbb Q}$ of discriminant $D$ and an Eichler order $\mathcal O$ of level $M$,
$\sum_{[J] \in \operatorname{Cls}\mathcal O} 1/w_J = \varphi(D)\psi(M)/12$. (Every order over $\mathbb Z$ is free, so the freeness
hypothesis of the number-field version holds automatically.) -/
@[kb "voight2021" "Theorem 25.3.18, p. 423; Proposition 26.6.4, p. 445"]
theorem eichlerMassFormulaEichlerOrdersRat_of (H : Wave6.MassSuperorder ℚ) (Hmax : EichlerMassFormulaRat) :
    EichlerMassFormulaEichlerOrdersRat := by
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom
      Rat.ringOfIntegersEquiv.symm.surjective
  intro a b ha hb hdef O 𝔐 hlev
  obtain ⟨e⟩ := nonempty_basis_of_isOrder (isOrder_of_isEichlerOrder hlev.1)
  obtain ⟨O₁, hmax, h⟩ := exists_maximal_clsMass_eq H ha hb hdef e hlev
  rw [h, Hmax a b ha hb hdef O₁ hmax]
  ring

end Main

end QuadFormsKB.Voight.Wave10

