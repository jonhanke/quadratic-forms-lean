/-
# Cassels, Chapter 9, §5: representations by the forms of a genus, lattice form

**Layer:** lattices `L : Lat F n` on a regular quadratic space $V = (F^n, Q)$ over a number field $F$ (Cassels: $F =
\mathbb Q$, $L = \mathbb Z^n$ with the form $f$); localizations `loc v L` at the finite primes; the genus
`SameGenus Q L M` (equal localizations up to local isometries, O'Meara 102A).

**Proves** the lattice forms of Cassels' Theorem 1.3 and Theorem 5.1 (Ch. 9, pp. 129, 143), for every $n \ge 1$:
* `exists_sameGenus_mem`: if $c = Q(x) \ne 0$ for some $x \in V$ and $c$ is represented by $L_\mathfrak p$ at every
  finite prime, then $x$ lies in some lattice $M$ of the genus of $L$;
* `exists_sameGenus_primitive`: if $a \ne 0$ is represented by $V$ at every infinite place and primitively by
  $L_\mathfrak p$ at every finite prime, then $a$ is primitively represented by some lattice $M$ of the genus of $L$.

*Proof (not Cassels').* Cassels proves Theorems 1.2, 1.3 and 5.1 together by induction on $n$ (Lemma 5.1: completing
the square, Witt's lemma, Lemma 4.2). Here the argument is adelic, as for Chapter 11, Theorem 7.1
(`exists_sameProperSpinorGenus_primitive`) but without the spinor norm: by the Hasse principle $a = Q(x)$ with
$x \in V$; $x$ is primitive in $L_\mathfrak p$ for almost all $\mathfrak p$ (`eventually_locPrimitive`); at the other
primes Witt's theorem (`exists_orth_mulVec_eq_local`) gives $\gamma_\mathfrak p \in O(V_\mathfrak p)$ with
$\gamma_\mathfrak p x = y_\mathfrak p$, a primitive representation of $a$ by $L_\mathfrak p$; the adele $\delta$ with
$\delta_\mathfrak p = \gamma_\mathfrak p^{-1}$ there and $1$ elsewhere moves $L$ to $M = \delta L$ in the genus of $L$
(`orbit_eq_genus`), and $x = \delta_\mathfrak p y_\mathfrak p$ is primitive in every $M_\mathfrak p$, hence in $M$
(`latPrimitive_of_forall_loc`). This is the argument of O'Meara 102:5 for one vector.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec7

open NumberField IsDedekindDomain Matrix Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Moving local representations onto $x$ by the adelic orthogonal group:** if $Q(x) \ne 0$ and $y_\mathfrak p \in
V_\mathfrak p$ has $Q(y_\mathfrak p) = Q(x)$ for every $\mathfrak p$, then for any property `good` of primes holding for
almost all $\mathfrak p$ there is $\delta \in O(V)(\mathbb A_f)$ with $\delta_\mathfrak p = 1$ where `good` holds and
$\delta_\mathfrak p y_\mathfrak p = x$ elsewhere. -/
theorem exists_oaf_move {x : Fin n → F} (hx0 : Q.evalIn F x ≠ 0) (good : HeightOneSpectrum (𝓞 F) → Prop)
    (hgood : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, good v)
    (y : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (hy : ∀ v, Q.evalIn (v.adicCompletion F) (y v) = algebraMap F _ (Q.evalIn F x)) :
    ∃ δ : OAf Q, ∀ v, (good v → δ v = 1) ∧
      (¬ good v → (((δ v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ y v = locVec v x) := by
  classical
  have hloc0 : ∀ v : HeightOneSpectrum (𝓞 F), Q.evalIn (v.adicCompletion F) (locVec v x) ≠ 0 := fun v => by
    rw [evalIn_locVec]; exact (map_ne_zero _).mpr hx0
  choose γ hγ hγx using fun v => exists_orth_mulVec_eq_local Q v (x := locVec v x) (y := y v)
    (by rw [evalIn_locVec, hy v]) (hloc0 v)
  obtain ⟨δ, hδ⟩ : ∃ δ : OAf Q, ∀ v, δ v = if good v then 1 else (⟨γ v, hγ v⟩ : orthGroup Q _)⁻¹ :=
    ⟨⟨fun v => if good v then 1 else (⟨γ v, hγ v⟩ : orthGroup Q _)⁻¹, by
      filter_upwards [hgood] with v hv
      simp only [hv, ↓reduceIte]
      exact (stdStab Q v).one_mem⟩, fun v => rfl⟩
  refine ⟨δ, fun v => ⟨fun hv => by rw [hδ v, if_pos hv], fun hv => ?_⟩⟩
  rw [hδ v, if_neg hv, ← hγx v, Subgroup.coe_inv, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mulVec]

/-- **Representations by the genus (lattice form of Cassels' Theorem 1.3):** if $c = Q(x) \ne 0$ with $x \in V$ and
$c$ is represented by $L_\mathfrak p$ at every finite prime, then $x$ lies in some lattice $M$ of the genus of $L$. -/
@[kb "cassels1978" "Ch. 9, Thm. 1.3, p. 129 (lattice form, over a number field)"]
theorem exists_sameGenus_mem (L : Lat F n) {c : F} (hc : c ≠ 0) {x : Fin n → F} (hx : Q.evalIn F x = c)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ y ∈ loc v L.1,
      Q.evalIn (v.adicCompletion F) y = algebraMap F (v.adicCompletion F) c) :
    ∃ M : Lat F n, SameGenus Q L.1 M.1 ∧ x ∈ M.1 := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  have hx0 : Q.evalIn F x ≠ 0 := hx ▸ hc
  have hxne : x ≠ 0 := by
    rintro rfl; apply hx0; simp [QuadForm.evalIn]
  choose y hyL hya using hloc
  obtain ⟨δ, hδ⟩ := exists_oaf_move Q hx0 (fun v => locVec v x ∈ loc v L.1)
    ((eventually_locPrimitive L.2 hxne).mono fun v hv => hv.1) y (fun v => by rw [hya v, hx])
  have hgen : latSMul Q δ L ∈ latGenus Q L := by
    rw [← orbit_eq_genus]; exact ⟨δ, rfl⟩
  refine ⟨latSMul Q δ L, hgen, ?_⟩
  rw [mem_iff_forall_loc (latSMul Q δ L).2]
  intro v
  rw [loc_latSMul]
  by_cases hv : locVec v x ∈ loc v L.1
  · rw [(hδ v).1 hv, OneMemClass.coe_one, locAct_one]
    exact hv
  · exact ⟨y v, hyL v, (hδ v).2 hv⟩

/-- **Primitive representations by the genus (lattice form of Cassels' Theorem 5.1):** *if $a \ne 0$ is represented by
$f$ over $\mathbb R$ and primitively over every $\mathbb Z_p$, then $a$ is primitively represented over $\mathbb Z$ by
some form in the genus of $f$.* Here $f$ is a lattice `L` on the regular space $(F^n, Q)$, the real condition is
`hinf` (representation by $V$ over every infinite completion), the local condition is `hloc` (a primitive vector
$y$ of $L_\mathfrak p$ with $Q(y) = a$, `LocPrimitive`), and the conclusion is a lattice $M$ in the genus of $L$ with a
primitive vector $x$ (`LatPrimitive`), $Q(x) = a$. (Cassels assumes the local condition only at $p \mid 2d$, resp.
$p \mid 2ad$ for $n = 2$, and shows that it holds automatically elsewhere; see `Ch9Sec5.lean`.) -/
@[kb "cassels1978" "Ch. 9, Thm. 5.1, p. 143 (lattice form, over a number field)"]
theorem exists_sameGenus_primitive (hQ : Q.Nondegenerate) (L : Lat F n) {a : F} (ha : a ≠ 0)
    (hinf : ∀ w : InfinitePlace F, Q.RepresentsIn w.Completion a)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ y, LocPrimitive v (loc v L.1) y ∧
      Q.evalIn (v.adicCompletion F) y = algebraMap F _ a) :
    ∃ M : Lat F n, SameGenus Q L.1 M.1 ∧ ∃ x, LatPrimitive M.1 x ∧ Q.evalIn F x = a := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨x, hxa⟩ : Q.RepresentsIn F a := by
    rw [represents_iff_everywhere_nf Q hQ a ha]
    intro w
    cases w with
    | infinite w => exact hinf w
    | finite v =>
      obtain ⟨y, -, hy⟩ := hloc v
      exact ⟨y, hy⟩
  have hxa' : Q.evalIn F x = a := by simpa using hxa
  have hx0 : Q.evalIn F x ≠ 0 := hxa' ▸ ha
  have hxne : x ≠ 0 := by
    rintro rfl; apply hx0; simp [QuadForm.evalIn]
  choose y hyp hya using hloc
  obtain ⟨δ, hδ⟩ := exists_oaf_move Q hx0 (fun v => LocPrimitive v (loc v L.1) (locVec v x))
    (eventually_locPrimitive L.2 hxne) y (fun v => by rw [hya v, hxa'])
  have hgen : latSMul Q δ L ∈ latGenus Q L := by
    rw [← orbit_eq_genus]; exact ⟨δ, rfl⟩
  refine ⟨latSMul Q δ L, hgen, x, ?_, hxa'⟩
  apply latPrimitive_of_forall_loc (latSMul Q δ L).2
  intro v
  rw [loc_latSMul]
  by_cases hv : LocPrimitive v (loc v L.1) (locVec v x)
  · rw [(hδ v).1 hv, OneMemClass.coe_one, locAct_one]
    exact hv
  · rw [← (hδ v).2 hv]
    exact (hyp v).locAct _

end QuadFormsKB.Lattices
