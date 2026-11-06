/-
# Cassels, Appendix A, §3: Watson's operation $\Lambda \mapsto \Lambda_p$

**Layer:** an integer-valued form $Q$ = `Q : QuadForm ℤ n` on the lattice $\Lambda = \mathbb Z^n$ (Cassels' $\phi$
on $\Lambda$; "integer-valued" is the library's integrality, Ch. 1, (2.17)); $H$ = `Q.hessian`, so
$Q(b + c) - Q(b) - Q(c) = b^{\mathsf T}Hc$.

**Defines** (Cassels, App. A, §3, p. 365) Watson's sublattice
$$\Lambda_p = \{c \in \Lambda : \phi(b + c) \equiv \phi(b) \pmod p \text{ for all } b \in \Lambda\}$$
(`watsonSub Q p`).

**Proves** the properties that Cassels states for it (p. 365, citing Ch. 8, Ex. 8):
* $\Lambda_p$ is a lattice with $p\Lambda \subseteq \Lambda_p \subseteq \Lambda$ (`watsonSub` is a submodule;
  `smul_mem_watsonSub`);
* $\phi(c) \equiv 0 \pmod p$ for $c \in \Lambda_p$, so $\psi = p^{-1}\phi$ is integer-valued on $\Lambda_p$
  (`dvd_eval_of_mem_watsonSub`);
* isomorphic lattices give isomorphic $\Lambda_p$ (`mem_watsonSub_iff_of_isometry`);
* if $p \nmid \det H$ then $\Lambda_p = p\Lambda$ (`mem_watsonSub_iff_of_not_dvd`; a reading of the partly lost
  footnote "$\mathcal G_p = \dots$ unless $p = 2$ or $p$ divides the determinant", since $\det H = 2^n d(\phi)$).

*Not formalized* (Theorem 3.1, $c(n) \to \infty$): that the genus of $\Lambda_p, \psi$ has at most as many classes as
the genus of $\Lambda, \phi$; the "local study" (Ch. 8, Ex. 8) showing that repeated operations reach a genus with a
lattice $r\Gamma_8 \perp A$, $r \ge (n - 6)/16$; and the count $1 + [r/2]$ of the classes
$j\Gamma_{16} \perp (r - 2j)\Gamma_8 \perp A$. The book only sketches these steps.
-/
import QuadFormsKB.Siegel.Genus

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.DefiniteForms

variable {n : ℕ}

/-- Polar identity over `ℤ`: $Q(b + c) - Q(b) - Q(c) = b^{\mathsf T} H c$. -/
private lemma eval_polar (Q : QuadForm ℤ n) (b c : Fin n → ℤ) :
    Q.eval (b + c) - Q.eval b - Q.eval c = b ⬝ᵥ (Q.hessian *ᵥ c) := by
  have h := Q.polar_eq_hessian ℤ b c
  simpa using h

/-- $Q(t c) = t^2 Q(c)$ over `ℤ`. -/
private lemma eval_smul' (Q : QuadForm ℤ n) (t : ℤ) (c : Fin n → ℤ) :
    Q.eval (t • c) = t ^ 2 * Q.eval c := by
  have h1 := Q.evalIn_eq_dotProduct ℤ (t • c)
  have h2 := Q.evalIn_eq_dotProduct ℤ c
  simp only [Algebra.algebraMap_self] at h1 h2
  show Q.evalIn ℤ (t • c) = t ^ 2 * Q.evalIn ℤ c
  rw [h1, h2, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul]
  ring

/-- $Q(0) = 0$. -/
private lemma eval_zero' (Q : QuadForm ℤ n) : Q.eval (0 : Fin n → ℤ) = 0 := by
  have := eval_smul' Q 0 (0 : Fin n → ℤ)
  simpa using this

/-- Expansion of $Q(b + t c) - Q(b)$. -/
private lemma eval_add_smul (Q : QuadForm ℤ n) (t : ℤ) (b c : Fin n → ℤ) :
    Q.eval (b + t • c) - Q.eval b = t * (b ⬝ᵥ (Q.hessian *ᵥ c)) + t ^ 2 * Q.eval c := by
  have h := eval_polar Q b (t • c)
  rw [Matrix.mulVec_smul, dotProduct_smul, eval_smul'] at h
  simp only [smul_eq_mul] at h
  linarith

/-- Membership criterion for Watson's sublattice. -/
private lemma watson_iff (Q : QuadForm ℤ n) (p : ℤ) (c : Fin n → ℤ) :
    (∀ b : Fin n → ℤ, p ∣ Q.eval (b + c) - Q.eval b) ↔
      p ∣ Q.eval c ∧ ∀ b : Fin n → ℤ, p ∣ b ⬝ᵥ (Q.hessian *ᵥ c) := by
  constructor
  · intro h
    have h0 : p ∣ Q.eval c := by
      have := h 0
      simpa [eval_zero'] using this
    refine ⟨h0, fun b => ?_⟩
    have h1 := h b
    have h2 := eval_polar Q b c
    have : b ⬝ᵥ (Q.hessian *ᵥ c) = (Q.eval (b + c) - Q.eval b) - Q.eval c := by linarith
    rw [this]
    exact dvd_sub h1 h0
  · rintro ⟨h0, h⟩ b
    have h2 := eval_polar Q b c
    have : Q.eval (b + c) - Q.eval b = b ⬝ᵥ (Q.hessian *ᵥ c) + Q.eval c := by linarith
    rw [this]
    exact dvd_add (h b) h0

/-- **Watson's sublattice** $\Lambda_p$ (Cassels, App. A, §3, p. 365): the $c \in \Lambda = \mathbb Z^n$ with
$Q(b + c) \equiv Q(b) \pmod p$ for every $b \in \Lambda$. -/
@[kb "cassels1978" "App. A, §3, p. 365 (Watson's operation: the lattice Λ_p)"]
def watsonSub (Q : QuadForm ℤ n) (p : ℤ) : Submodule ℤ (Fin n → ℤ) where
  carrier := {c | ∀ b : Fin n → ℤ, p ∣ Q.eval (b + c) - Q.eval b}
  add_mem' := by
    intro c c' hc hc' b
    have e : Q.eval (b + (c + c')) - Q.eval b
        = (Q.eval ((b + c) + c') - Q.eval (b + c)) + (Q.eval (b + c) - Q.eval b) := by
      rw [add_assoc]; ring
    rw [e]
    exact dvd_add (hc' (b + c)) (hc b)
  zero_mem' := by
    intro b
    simp
  smul_mem' := by
    intro k c hc
    have h := (watson_iff Q p c).1 hc
    refine (watson_iff Q p (k • c)).2 ⟨?_, fun b => ?_⟩
    · rw [eval_smul']
      exact Dvd.dvd.mul_left h.1 _
    · rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
      exact Dvd.dvd.mul_left (h.2 b) _

theorem mem_watsonSub {Q : QuadForm ℤ n} {p : ℤ} {c : Fin n → ℤ} :
    c ∈ watsonSub Q p ↔ ∀ b : Fin n → ℤ, p ∣ Q.eval (b + c) - Q.eval b := Iff.rfl

/-- **$p\Lambda \subseteq \Lambda_p$** (Cassels, App. A, §3, p. 365). -/
@[kb "cassels1978" "App. A, §3, p. 365 (Λ_p is a lattice, pΛ ⊆ Λ_p ⊆ Λ)"]
theorem smul_mem_watsonSub (Q : QuadForm ℤ n) (p : ℤ) (c : Fin n → ℤ) : p • c ∈ watsonSub Q p := by
  intro b
  rw [eval_add_smul]
  exact dvd_add (Dvd.intro _ rfl) (Dvd.intro (p * Q.eval c) (by ring))

/-- **$\phi(c) \equiv 0 \pmod p$ on $\Lambda_p$** (Cassels, App. A, §3, p. 365), so $\psi = p^{-1}\phi$ is
integer-valued on $\Lambda_p$. -/
@[kb "cassels1978" "App. A, §3, p. 365 (φ(c) ≡ 0 mod p on Λ_p; ψ = p⁻¹φ is integer-valued)"]
theorem dvd_eval_of_mem_watsonSub {Q : QuadForm ℤ n} {p : ℤ} {c : Fin n → ℤ} (hc : c ∈ watsonSub Q p) :
    p ∣ Q.eval c := ((watson_iff Q p c).1 hc).1

/-- **Isomorphic lattices produce isomorphic $\Lambda_p$** (Cassels, App. A, §3, p. 365): if $g \in \mathrm{GL}_n(\mathbb Z)$
and $Q(gx) = Q'(x)$, then $g$ maps $\Lambda_p(Q')$ onto $\Lambda_p(Q)$. -/
@[kb "cassels1978" "App. A, §3, p. 365 (isomorphic lattices Λ produce isomorphic lattices Λ_p)"]
theorem mem_watsonSub_iff_of_isometry {Q Q' : QuadForm ℤ n} (p : ℤ) (g : GL (Fin n) ℤ)
    (hg : ∀ x, Q.eval (g.val *ᵥ x) = Q'.eval x) (c : Fin n → ℤ) :
    g.val *ᵥ c ∈ watsonSub Q p ↔ c ∈ watsonSub Q' p := by
  have key : ∀ b' : Fin n → ℤ, Q.eval (g.val *ᵥ b' + g.val *ᵥ c) - Q.eval (g.val *ᵥ b')
      = Q'.eval (b' + c) - Q'.eval b' := by
    intro b'
    rw [← Matrix.mulVec_add, hg, hg]
  constructor
  · intro h b'
    rw [← key]
    exact h _
  · intro h b
    have hb : g.val *ᵥ ((g⁻¹).val *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec]
      simp
    have := h ((g⁻¹).val *ᵥ b)
    rw [← key, hb] at this
    exact this

/-- **$\Lambda_p = p\Lambda$ when $p \nmid \det H$** (Cassels, App. A, §3, footnote on p. 365, partly lost): then
$c \in \Lambda_p$ if and only if $c \in p\Lambda$. -/
@[kb "cassels1978" "App. A, §3, footnote on p. 365 (Λ_p = pΛ unless p = 2 or p divides the determinant)"]
theorem mem_watsonSub_iff_of_not_dvd {Q : QuadForm ℤ n} {p : ℤ} (hp : Prime p) (hdet : ¬ p ∣ Q.hessian.det)
    (c : Fin n → ℤ) : c ∈ watsonSub Q p ↔ ∃ c' : Fin n → ℤ, c = p • c' := by
  constructor
  · intro hc
    obtain ⟨h0, h⟩ := (watson_iff Q p c).1 hc
    have hH : ∀ i, p ∣ (Q.hessian *ᵥ c) i := by
      intro i
      have := h (Pi.single i 1)
      simpa [dotProduct_single] using this
    have hd : ∀ i, p ∣ Q.hessian.det * c i := by
      intro i
      have e : Q.hessian.det • c = (Q.hessian.adjugate) *ᵥ (Q.hessian *ᵥ c) := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
        simp
      have := congrFun e i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (hH j) _
    have hc' : ∀ i, p ∣ c i := fun i => (hp.dvd_or_dvd (hd i)).resolve_left hdet
    refine ⟨fun i => c i / p, funext fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hc' i)).symm
  · rintro ⟨c', rfl⟩
    exact smul_mem_watsonSub Q p c'

end QuadFormsKB.DefiniteForms
