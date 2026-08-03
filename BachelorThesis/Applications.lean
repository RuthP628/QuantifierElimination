import Mathlib
import BachelorThesis.QuantifierElimination

set_option linter.style.whitespace false

open FirstOrder
open Language
open Theory

#check Language.order

namespace FirstOrder
namespace Language
namespace Theory
namespace dlo

universe u v
variable (L : Language.{u, v}) [L.IsOrdered]

/-- The interpretation of the `≤`-symbol in a model of DLO. -/
def le (M : Type*) [L.Structure M] [M ⊨ L.dlo] : M → M → Prop := by
  rename_i _ struc _
  intro m₁ m₂
  let v : Fin 2 → M := fun x ↦ if h : x = 0 then m₁ else m₂
  use struc.RelMap leSymb v

/-- The interpretation of the `≤`-symbol in a model of DLO is reflexive. -/
lemma le_refl (M : Type*) [L.Structure M] [M ⊨ L.dlo] :
  ∀ (a : M), (Theory.dlo.le L M) a a := by
    rename_i _ _ is_model
    unfold dlo at is_model; unfold linearOrderTheory at is_model
    unfold partialOrderTheory at is_model; unfold preorderTheory at is_model
    have h : Sentence.Realize M (@leSymb L _).reflexive := by simp_all
    unfold Relations.reflexive at h; unfold Sentence.Realize at h; unfold Formula.Realize at h
    rw [BoundedFormula.realize_all] at h
    intro m
    specialize h m
    unfold le
    simp_all only [Set.union_insert, Set.union_singleton, model_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, Relations.realize_total,
      Relations.realize_antisymmetric, Relations.realize_reflexive, Relations.realize_transitive,
      forall_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.comp_apply,
      BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inr, dite_eq_ite, ite_self]
    have this : @Matrix.vecCons (↑M) 1 (@Fin.snoc 0 (fun a ↦ ↑M) default m 0 )
      ![@Fin.snoc 0 (fun a ↦ ↑M) default m 0 ] = fun (x : Fin (Nat.succ 1)) ↦ m :=
        List.ofFn_inj.mp rfl
    rwa [← this]

/-- The interpretation of the `≤`-symbol in a model of DLO is transitive. -/
lemma le_trans (M : Type*) [L.Structure M] [M ⊨ L.dlo] :
  ∀ a b c : M, (Theory.dlo.le L M a b) → (Theory.dlo.le L M b c) → (Theory.dlo.le L M a c) := by
    rename_i _ _ is_model
    unfold le
    intro m₁ m₂ m₃ hm₁m₂ hm₂m₃
    have h : Sentence.Realize M (@leSymb L _).transitive := by
      unfold dlo at is_model; unfold linearOrderTheory at is_model
      unfold partialOrderTheory at is_model; unfold preorderTheory at is_model
      simp_all
    simp_all only [Fin.isValue, dite_eq_ite]
    unfold Relations.transitive at h; unfold Sentence.Realize at h; unfold Formula.Realize at h
    rw [BoundedFormula.realize_all] at h
    specialize h m₁
    rw [BoundedFormula.realize_all] at h
    specialize h m₂
    rw [BoundedFormula.realize_all] at h
    specialize h m₃
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.comp_apply,
      BoundedFormula.realize_imp, BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inr,
      Fin.snoc_apply_zero] at h
    have this₁ : ![@Fin.snoc 0 (fun a ↦ ↑M) default m₁ 0,
      @Fin.snoc 2 (fun a ↦ ↑M) (Fin.snoc (Fin.snoc default m₁) m₂) m₃ 1]
      = fun (x : Fin (Nat.succ 1)) ↦ if x = 0 then m₁ else m₂ := List.ofFn_inj.mp rfl
    have this₂ : ![@Fin.snoc 2 (fun a ↦ ↑M) (Fin.snoc (Fin.snoc default m₁) m₂) m₃ 1,
      @Fin.snoc 2 (fun a ↦ ↑M) (Fin.snoc (Fin.snoc default m₁) m₂) m₃ 2 ]
      = fun x ↦ if x = 0 then m₂ else m₃ := List.ofFn_inj.mp rfl
    have this₃ : ![@Fin.snoc 0 (fun a ↦ ↑M) default m₁ 0,
      @Fin.snoc 2 (fun a ↦ ↑M) (Fin.snoc (Fin.snoc default m₁) m₂) m₃ 2]
      = fun x ↦ if x = 0 then m₁ else m₃ := List.ofFn_inj.mp rfl
    rw [this₁, this₂, this₃] at h
    exact h hm₁m₂ hm₂m₃

/-- The interpretation of the `≤`-symbol in a model of DLO is antisymmetric. -/
lemma le_antisymm (M : Type*) [L.Structure M] [M ⊨ L.dlo] :
  ∀ (a b : M), dlo.le L M a b → dlo.le L M b a → a = b := by
    unfold dlo.le
    intro a b hab hba
    rename_i _ _ is_model
    unfold dlo at is_model; unfold linearOrderTheory at is_model;
    unfold partialOrderTheory at is_model
    have hM : M ⊨ (@leSymb L _).antisymmetric := by simp_all
    unfold Relations.antisymmetric at hM; unfold Sentence.Realize at hM
    unfold Formula.Realize at hM
    rw [BoundedFormula.realize_all] at hM
    specialize hM a
    rw [BoundedFormula.realize_all] at hM
    specialize hM b
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.comp_apply,
      BoundedFormula.realize_imp, BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inr,
      Fin.snoc_apply_zero, BoundedFormula.realize_bdEqual] at hM
    have this₁ : ![@Fin.snoc 0 (fun a ↦ M) default a 0,
      @Fin.snoc 1 (fun a ↦ M) (Fin.snoc default a) b 1]
      = fun x ↦ if h : x = 0 then a else b := List.ofFn_inj.mp rfl
    have this₂ : ![@Fin.snoc 1 (fun a ↦ M) (Fin.snoc default a) b 1,
    @Fin.snoc 0 (fun a ↦ M) default a 0]
    = fun x ↦ if h : x = 0 then b else a := List.ofFn_inj.mp rfl
    rw [this₁, this₂] at hM
    simp_all only [Set.union_insert, Set.union_singleton, model_iff, Set.mem_insert_iff,
      forall_eq_or_imp, Relations.realize_total, Relations.realize_antisymmetric, Fin.isValue,
      dite_eq_ite, Nat.succ_eq_add_one, Nat.reduceAdd, forall_const]
    exact ((fun a ↦ hM) ∘ fun a ↦ L) L

/-- Any two elements `a`, `b` in a model of DLO are comparable w.r.t.
the interpretation of the `≤`-symbol. -/
lemma le_total (M : Type*)  [L.Structure M] [M ⊨ L.dlo] :
  ∀ a b : M, dlo.le L M a b ∨ dlo.le L M b a := by
    intro a b
    unfold dlo.le
    rename_i _ _ is_model
    unfold dlo at is_model; unfold linearOrderTheory at is_model
    have hM : M ⊨ (@leSymb L _).total := by simp_all
    unfold Relations.total at hM
    unfold Sentence.Realize at hM; unfold Formula.Realize at hM
    rw [BoundedFormula.realize_all] at hM
    specialize hM a
    rw [BoundedFormula.realize_all] at hM
    specialize hM b
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.comp_apply,
      BoundedFormula.realize_sup, BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inr,
      Fin.snoc_apply_zero] at hM
    obtain hM₁ | hM₂ := hM
    · left
      have this : ![@Fin.snoc 0 (fun a ↦ M) default a 0,
      @Fin.snoc 1 (fun a ↦ M) (Fin.snoc default a) b 1] = fun x ↦ if h : x = 0 then a else b :=
        List.ofFn_inj.mp rfl
      rwa [← this]
    · right
      have this : ![@Fin.snoc 1 (fun a ↦ M) (Fin.snoc default a) b 1,
      @Fin.snoc 0 (fun a ↦ M) default a 0] = fun x ↦ if h : x = 0 then b else a :=
        List.ofFn_inj.mp rfl
      rwa [← this]

end dlo
end Theory

namespace order

/-- Let `M`, `N` be two linear-ordered structures without a minimal element.
Moreover, let `f : M → N` be a partial isomorphism with finite domain.
Then, `f` can be extended to an element that is smaller than all elements in the domain of `f`. -/
lemma dlo_PartialIso_extends_lt_of_finite_source {M : Type*} {N : Type*}
  [Nonempty M] [Nonempty N] [LinearOrder M] [LinearOrder N]
  [Language.order.Structure M] [Language.order.Structure N]
  [Language.order.OrderedStructure M] [Language.order.OrderedStructure N]
  [NoBotOrder M] [NoBotOrder N]
  (f : Language.order.PartialIso M N) (hf₁ : Nonempty f.source) (hf₂ : Finite f.source) (m : M)
  (hm : ∀ m' ∈ f.source, m < m') :
    ∃ g : PartialIso M N, m ∈ g.source ∧ f ≤ g := by
      let source_set : Finset M := Set.Finite.toFinset hf₂
      let m_min := source_set.min
      have hf₃ : Finset.Nonempty source_set := by
        apply Classical.choice at hf₁
        use hf₁
        have hf₁' : (hf₁ : M) ∈ f.source := Subtype.coe_prop hf₁
        exact (Set.Finite.mem_toFinset hf₂).mpr hf₁'
      have h_m_min := Finset.min_of_nonempty hf₃
      -- We define `m_min'` to be the minimal element of the domain of `f`.
      obtain ⟨ m_min', h_m_min' ⟩ := h_m_min
      have h_m_min'' : m_min' ∈ f.source := by
        have h_m_min''₁ : m_min' ∈ source_set := Finset.mem_of_min h_m_min'
        have h_source_set : (source_set : Set M) ⊆ f.source :=
          Set.Finite.subset_toFinset.mp fun ⦃x⦄ a ↦ a
        exact Set.mem_of_subset_of_mem h_source_set h_m_min''₁
      -- Let `n_min'` be the image of `m_min'` under `f`.
      let n_min' := f.toFun m_min'
      have h_n_min' : n_min' ∈ f.target := by
        unfold n_min'
        simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype,
          PartialEquiv.map_source]
      -- Then, `n_min'` is the minimal element of the codomain of `f`.
      have h_n_min'₁ : ∀ n' ∈ f.target, n_min' ≤ n' := by
        intro n' hn'
        let m' := f.invFun n'
        have hm'₁ : m' ∈ f.source := f.map_target' hn'
        have hm'₂ : ∀ m' ∈ source_set, m_min' ≤ m' :=
          fun m' a ↦ Finset.min_le_of_eq a h_m_min'
        have hm'₃ : m' ∈ source_set := (Set.Finite.mem_toFinset hf₂).mpr hm'₁
        specialize hm'₂ m' hm'₃
        have hm'₄ := f.map_rel' (@IsOrdered.leSymb Language.order _)
          (fun x ↦ if h : x = 0 then m_min' else m')
        have hm'₅ : ∀ (x : Fin 2), (if h : x = 0 then m_min' else m') ∈ f.source := by
          intro x
          by_cases hx : x = 0
          · simp_all
          · simp_all
        specialize hm'₄ hm'₅
        simp only [Fin.isValue, dite_eq_ite, relMap_leSymb, ↓reduceIte, one_ne_zero,
          Function.comp_apply] at hm'₄
        apply hm'₄.1 at hm'₂
        aesop
      -- Since the linear order on `N` does not have a minimal element,
      -- there is `n ∈ N` that is strictly smaller than `n_min'`.
      have hn : ∃ n : N, n < n_min' := by
        rename_i hN
        have hN' := hN.exists_not_ge n_min'
        obtain ⟨ n, hn ⟩ := hN'
        use n
        simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, not_le]
      obtain ⟨ n, hn₁ ⟩ := hn
      -- Then, `n` is strictly smaller than all elements in the codomain of `f`.
      have hn₂ : ∀ n' ∈ f.target, n < n' := by
        intro n' hn'
        specialize h_n_min'₁ n' hn'
        exact Std.lt_of_lt_of_le hn₁ h_n_min'₁
      -- Now, we define a partial isomorphism `g` by extending the domain of `f` to include `m`.
      -- Here, `m` gets mapped to `n`.
      let g : Language.order.PartialIso M N := {
        toFun := fun x ↦ if h : x = m then n else f.toFun x
        invFun := fun x ↦ if h : x = n then m else f.invFun x
        source := f.source ∪ {m}
        target := f.target ∪ {n}
        map_source' := by
          intro x hx
          obtain hx₁ | hx₂ := hx
          · have hx₃ : x ≠ m := Ne.symm (Std.ne_of_lt (hm x hx₁))
            simp_all
          · simp_all
        map_target' := by
          intro x hx
          obtain hx₁ | hx₂ := hx
          · have hx₃ : x ≠ n :=  Ne.symm (Std.ne_of_lt (hn₂ x hx₁))
            simp_all
          · simp_all
        left_inv' := by
          intro x hx
          obtain hx₁ | hx₂ := hx
          · have hx₃ : x ≠ m := Ne.symm (Std.ne_of_lt (hm x hx₁))
            simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, ne_eq,
              ↓reduceDIte, PartialEquiv.invFun_as_coe, PartialEquiv.left_inv, dite_eq_ite,
              ite_eq_right_iff]
            intro hx₄
            have hx₅ : n ∉ f.target := by grind
            rw [← hx₄] at hx₅
            have hx₆ : f.toFun x ∈ f.target := f.map_source hx₁
            contradiction
          · simp_all
        right_inv' := by
          intro x hx
          obtain hx₁ | hx₂ := hx
          · have hx₃ : x ≠ n := Ne.symm (Std.ne_of_lt (hn₂ x hx₁))
            simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, ne_eq,
              ↓reduceDIte, PartialEquiv.invFun_as_coe, PartialEquiv.right_inv, dite_eq_ite,
              ite_eq_right_iff]
            intro hx₄
            have hx₅ : m ∉ f.source := by grind
            rw [← hx₄] at hx₅
            have hx₆ : f.invFun x ∈ f.source := f.map_target hx₁
            contradiction
          · simp_all
        map_fun' := by
          intros
          trivial
        map_rel' := by
          intro n₁ r a ha
          cases r
          by_cases ha₁ : a 0 ∈ f.source
          · by_cases ha₂ : a 1 ∈ f.source
            · have ha₃ : ∀ x : Fin 2, a x ∈ f.source := by
                intro x
                by_cases h : x = 0
                · rw [h]
                  exact ha₁
                · grind
              have ha₄ := f.map_rel' orderRel.le a ha₃
              have ha₅ : ((fun x ↦ if h : x = m then n else f.toFun x) ∘ a) = f.toFun ∘ a := by
                  ext x
                  grind
              constructor
              · intro ha₆
                apply ha₄.1 at ha₆
                rwa [ha₅]
              · intro ha₆
                apply ha₄.2
                rwa [← ha₅]
            · have ha₃ : a 1 = m := Or.resolve_left (ha 1) ha₂
              specialize hm (a 0) ha₁
              rw [← ha₃] at hm
              constructor
              · intro ha₄
                have ha₅ : orderRel.le = @IsOrdered.leSymb Language.order _ :=
                  ((fun a ↦ a) ∘ fun a ↦ a) rfl
                rw [ha₅] at ha₄
                have ha₆ : a 0 ≤ a 1 := by simp_all only [orderedStructure_iff, orderLHom_order,
                  nonempty_subtype, Fin.isValue, Set.union_singleton, Set.mem_insert_iff,
                  Fin.forall_fin_two, or_true, true_or, and_self, relMap_leSymb]
                grind
              · intro ha₄
                have ha₅ : orderRel.le = @IsOrdered.leSymb Language.order _ :=
                 ((fun a ↦ a) ∘ fun a ↦ a) rfl
                rw [ha₅] at ha₄
                have ha₆ : a 0 ≠ m := by rw [← ha₃]; exact ne_of_mem_of_not_mem ha₁ ha₂
                simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, Fin.isValue,
                  Set.union_singleton, Set.mem_insert_iff, Fin.forall_fin_two, or_true, true_or,
                  and_self, dite_eq_ite, relMap_leSymb, Function.comp_apply, ↓reduceIte, ne_eq,
                  ge_iff_le]
                have ha₇ : f.toFun (a 0) ∈ f.target :=
                  PartialEquiv.map_source f.toPartialEquiv ha₁
                specialize hn₂ (f.toFun (a 0)) ha₇
                grind
          · have ha₃ : a 0 = m := Or.resolve_left (ha 0) ha₁
            by_cases ha₂ : a 1 ∈ f.source
            · specialize hm (a 1) ha₂
              rw [← ha₃] at hm
              have ha₄ : orderRel.le = @IsOrdered.leSymb Language.order _ :=
                ((fun a ↦ a) ∘ fun a ↦ a) rfl
              rw [ha₄]
              constructor
              · intro ha₅
                have ha₆ : a 1 ≠ m := by grind
                simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, Fin.isValue,
                  Set.union_singleton, Set.mem_insert_iff, Fin.forall_fin_two, true_or, or_true,
                  and_self, relMap_leSymb, ne_eq, dite_eq_ite, Function.comp_apply, ↓reduceIte,
                  ge_iff_le]
                have ha₇ : f.toFun (a 1) ∈ f.target := by simp_all only [Fin.isValue,
                  PartialEquiv.map_source]
                specialize hn₂ (f.toFun (a 1)) ha₇
                exact Std.le_of_lt hn₂
              · intro ha₅
                simp only [relMap_leSymb, Fin.isValue]
                exact Std.le_of_lt hm
            · have ha₄ : a 1 = m := Or.resolve_left (ha 1) ha₂
              have ha₅ : orderRel.le = @IsOrdered.leSymb Language.order _ :=
                ((fun a ↦ a) ∘ fun a ↦ a) rfl
              rw [ha₅]
              simp_all
      }
      use g
      constructor
      · exact Set.mem_union_right f.source rfl
      · apply (PartialIso.le_def M N f g).2
        constructor
        · exact Set.subset_union_left
        · intro x hx
          grind


/-- Let `M`, `N` be two linear-ordered structures without a maximal elment.
Moreover, let `f : M → N` be a partial isomorphism with finite domain.
Then, `f` can be extended to an element that is greater than all elements in the domain of `f`. -/
lemma dlo_PartialIso_extends_gt_of_finite_source {M : Type*} {N : Type*}
  [Nonempty M] [Nonempty N] [LinearOrder M] [LinearOrder N]
  [Language.order.Structure M] [Language.order.Structure N]
  [Language.order.OrderedStructure M] [Language.order.OrderedStructure N]
  [NoTopOrder M] [NoTopOrder N]
  (f : Language.order.PartialIso M N) (hf₁ : Nonempty f.source) (hf₂ : Finite f.source) (m : M)
  (hm : ∀ m' ∈ f.source, m' < m) :
    ∃ g : PartialIso M N, m ∈ g.source ∧ f ≤ g := by
      let source_set : Finset M := Set.Finite.toFinset hf₂
      let m_max := source_set.max
      have hf₃ : Finset.Nonempty source_set := by
        apply Classical.choice at hf₁
        use hf₁
        have hf₁' : (hf₁ : M) ∈ f.source := Subtype.coe_prop hf₁
        exact (Set.Finite.mem_toFinset hf₂).mpr hf₁'
      have h_m_max := Finset.max_of_nonempty hf₃
      -- We define `m_max'` to be the maximal element of the domain of `f`.
      obtain ⟨ m_max', h_m_max' ⟩ := h_m_max
      have h_m_max'' : m_max' ∈ f.source := by
        have h_m_max''₁ : m_max' ∈ source_set := Finset.mem_of_max h_m_max'
        have h_source_set : (source_set : Set M) ⊆ f.source :=
          Set.Finite.subset_toFinset.mp fun ⦃x⦄ a ↦ a
        exact Set.mem_of_subset_of_mem h_source_set h_m_max''₁
      -- Let `n_max'` be the image of `m_max'` under `f`.
      let n_max' := f.toFun m_max'
      have h_n_max' : n_max' ∈ f.target := by
        unfold n_max'
        simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype,
          PartialEquiv.map_source]
      -- Then, `n_max'` is the maximal element of the codomain of `f`.
      have h_n_max'₁ : ∀ n' ∈ f.target, n' ≤ n_max' := by
        intro n' hn'
        let m' := f.invFun n'
        have hm'₁ : m' ∈ f.source := f.map_target' hn'
        have hm'₂ : ∀ m' ∈ source_set, m' ≤ m_max' :=
          fun m' a ↦ Finset.le_max_of_eq a h_m_max'
        have hm'₃ : m' ∈ source_set := (Set.Finite.mem_toFinset hf₂).mpr hm'₁
        specialize hm'₂ m' hm'₃
        have hm'₄ := f.map_rel' (@IsOrdered.leSymb Language.order _)
          (fun x ↦ if h : x = 0 then m' else m_max')
        have hm'₅ : ∀ (x : Fin 2), (if h : x = 0 then m' else m_max') ∈ f.source := by
          intro x
          by_cases hx : x = 0
          · simp_all
          · simp_all
        specialize hm'₄ hm'₅
        simp only [Fin.isValue, dite_eq_ite, relMap_leSymb, ↓reduceIte, one_ne_zero,
          Function.comp_apply] at hm'₄
        apply hm'₄.1 at hm'₂
        aesop
      -- Since the linear order on `N` does not have a maximal element,
      -- there is `n ∈ N` that is strictly greater than `n_min'`.
      have hn : ∃ n : N, n_max' < n := by
        rename_i hN
        have hN' := hN.exists_not_le n_max'
        obtain ⟨ n, hn ⟩ := hN'
        use n
        simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, not_le]
      obtain ⟨ n, hn₁ ⟩ := hn
      -- Then, `n` is strictly greater than all elements in the codomain of `f`.
      have hn₂ : ∀ n' ∈ f.target, n' < n := by
        intro n' hn'
        specialize h_n_max'₁ n' hn'
        exact Std.lt_of_le_of_lt h_n_max'₁ hn₁
      -- Now, we define a partial isomorphism `g` by extending the domain of `f` to include `m`.
      -- Here, `m` gets mapped to `n`.
      let g : Language.order.PartialIso M N := {
        toFun := fun x ↦ if h : x = m then n else f.toFun x
        invFun := fun x ↦ if h : x = n then m else f.invFun x
        source := f.source ∪ {m}
        target := f.target ∪ {n}
        map_source' := by
          intro x hx
          obtain hx₁ | hx₂ := hx
          · have hx₃ : x ≠ m := Std.ne_of_lt (hm x hx₁)
            simp_all
          · simp_all
        map_target' := by
          intro x hx
          obtain hx₁ | hx₂ := hx
          · have hx₃ : x ≠ n :=  Std.ne_of_lt (hn₂ x hx₁)
            simp_all
          · simp_all
        left_inv' := by
          intro x hx
          obtain hx₁ | hx₂ := hx
          · have hx₃ : x ≠ m := Std.ne_of_lt (hm x hx₁)
            simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, ne_eq,
              ↓reduceDIte, PartialEquiv.invFun_as_coe, PartialEquiv.left_inv, dite_eq_ite,
              ite_eq_right_iff]
            intro hx₄
            have hx₅ : n ∉ f.target := by grind
            rw [← hx₄] at hx₅
            have hx₆ : f.toFun x ∈ f.target := f.map_source hx₁
            contradiction
          · simp_all
        right_inv' := by
          intro x hx
          obtain hx₁ | hx₂ := hx
          · have hx₃ : x ≠ n := Std.ne_of_lt (hn₂ x hx₁)
            simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, ne_eq,
              ↓reduceDIte, PartialEquiv.invFun_as_coe, PartialEquiv.right_inv, dite_eq_ite,
              ite_eq_right_iff]
            intro hx₄
            have hx₅ : m ∉ f.source := by grind
            rw [← hx₄] at hx₅
            have hx₆ : f.invFun x ∈ f.source := f.map_target hx₁
            contradiction
          · simp_all
        map_fun' := by
          intros
          trivial
        map_rel' := by
          intro n₁ r a ha
          cases r
          by_cases ha₁ : a 0 ∈ f.source
          · by_cases ha₂ : a 1 ∈ f.source
            · have ha₃ : ∀ x : Fin 2, a x ∈ f.source := by
                intro x
                by_cases h : x = 0
                · rw [h]
                  exact ha₁
                · grind
              have ha₄ := f.map_rel' orderRel.le a ha₃
              have ha₅ : ((fun x ↦ if h : x = m then n else f.toFun x) ∘ a) = f.toFun ∘ a := by
                  ext x
                  grind
              constructor
              · intro ha₆
                apply ha₄.1 at ha₆
                rwa [ha₅]
              · intro ha₆
                apply ha₄.2
                rwa [← ha₅]
            · have ha₃ : a 1 = m := Or.resolve_left (ha 1) ha₂
              specialize hm (a 0) ha₁
              have ha₄ : orderRel.le = @IsOrdered.leSymb Language.order _ :=
                 ((fun a ↦ a) ∘ fun a ↦ a) rfl
              rw [ha₄]
              constructor
              · intro ha₅
                have ha₆ : a 0 ≠ m := Std.ne_of_lt hm
                simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, Fin.isValue,
                  Set.union_singleton, Set.mem_insert_iff, Fin.forall_fin_two, or_true, true_or,
                  and_self, relMap_leSymb, ne_eq, dite_eq_ite, Function.comp_apply, ↓reduceIte,
                  ge_iff_le]
                have ha₇ : f.toFun (a 0) ∈ f.target :=
                  PartialEquiv.map_source f.toPartialEquiv ha₁
                specialize hn₂ (f.toFun (a 0)) ha₇
                exact Std.le_of_lt hn₂
              · intro ha₅
                simp only [relMap_leSymb, Fin.isValue]
                rw [ha₃]
                exact Std.le_of_lt hm
          · have ha₃ : a 0 = m := Or.resolve_left (ha 0) ha₁
            by_cases ha₂ : a 1 ∈ f.source
            · specialize hm (a 1) ha₂
              rw [← ha₃] at hm
              have ha₄ : orderRel.le = @IsOrdered.leSymb Language.order _ :=
                ((fun a ↦ a) ∘ fun a ↦ a) rfl
              rw [ha₄]
              constructor
              · intro ha₅
                simp only [relMap_leSymb, Fin.isValue] at ha₅
                grind
              · intro ha₅
                rw [ha₃] at hm
                have ha₆ : a 1 ≠ m := Std.ne_of_lt hm
                simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, Fin.isValue,
                  Set.union_singleton, Set.mem_insert_iff, Fin.forall_fin_two, true_or, or_true,
                  and_self, dite_eq_ite, relMap_leSymb, Function.comp_apply, ↓reduceIte, ne_eq,
                  ge_iff_le]
                have ha₇ : f.toFun (a 1) ∈ f.target :=
                  PartialEquiv.map_source f.toPartialEquiv ha₂
                specialize hn₂ (f.toFun (a 1)) ha₇
                exact le_imp_le_of_lt_imp_lt (fun a ↦ hn₂) ha₅
            · have ha₄ : a 1 = m := Or.resolve_left (ha 1) ha₂
              have ha₅ : orderRel.le = @IsOrdered.leSymb Language.order _ :=
                ((fun a ↦ a) ∘ fun a ↦ a) rfl
              rw [ha₅]
              simp_all
      }
      use g
      constructor
      · exact Set.mem_union_right f.source rfl
      · apply (PartialIso.le_def M N f g).2
        constructor
        · exact Set.subset_union_left
        · intro x hx
          grind

/-- Let `M`, `N` be two densely-ordered structures.
Moreover, let `f : M → N` be a partial isomorphism with finite domain.
Then, `f` can be extended to an element that is
neither greater than all elements in the domain of `f`
nor smaller than all elements in the domain of `f`. -/
lemma dlo_PartialIso_extends_between_of_finite_source {M : Type*} {N : Type*}
  [Nonempty M] [Nonempty N] [LinearOrder M] [LinearOrder N]
  [Language.order.Structure M] [Language.order.Structure N]
  [Language.order.OrderedStructure M] [Language.order.OrderedStructure N]
  [DenselyOrdered M] [DenselyOrdered N]
  (f : Language.order.PartialIso M N) (hf₁ : Nonempty f.source) (hf₂ : Finite f.source) (m : M)
  (hm : (∃ m' ∈ f.source, m' < m) ∧ (∃ m' ∈ f.source, m < m')) (hm' : m ∉ f.source) :
    ∃ g : PartialIso M N, m ∈ g.source ∧ f ≤ g := by
      obtain ⟨ hm₁ , hm₂ ⟩ := hm
      let lt_set : Set M := {x | x ∈ f.source ∧ x < m}
      let gt_set : Set M := {x | x ∈ f.source ∧ m < x}
      have h_lt_set := (Finite.Set.finite_sep f.source fun a ↦ a < m)
      have h_gt_set := Finite.Set.finite_sep f.source (LT.lt m)
      let lt_finset := Set.Finite.toFinset h_lt_set
      let gt_finset := Set.Finite.toFinset h_gt_set
      let lt_max_m := lt_finset.max
      let gt_min_m := gt_finset.min
      have h_lt₁ : Finset.Nonempty lt_finset := by
        obtain ⟨ m₁, hm₁ ⟩ := hm₁
        have hm₁' : m₁ ∈ lt_set := by
          unfold lt_set
          simp_all
        use m₁
        exact (Set.Finite.mem_toFinset (Finite.Set.finite_sep f.source fun a ↦ a < m)).mpr hm₁
      have h_gt₁ : Finset.Nonempty gt_finset := by
        obtain ⟨ m₂, hm₂ ⟩ := hm₂
        have hm₂' : m₂ ∈ gt_set := by
          unfold gt_set
          simp_all
        use m₂
        exact (Set.Finite.mem_toFinset h_gt_set).mpr hm₂
      have h_lt_max_m := Finset.max_of_nonempty h_lt₁
      have h_gt_min_m := Finset.min_of_nonempty h_gt₁
      obtain ⟨ lt_max_m', h_lt_max_m' ⟩ := h_lt_max_m
      obtain ⟨ gt_min_m', h_gt_min_m' ⟩ := h_gt_min_m
      have h_lt_max_m'₁ : ∀ m' ∈ lt_finset, m' ≤ lt_max_m' := by
        intro m' hm'
        exact Finset.le_max_of_eq hm' h_lt_max_m'
      have h_lt_min_m'₁ : ∀ m' ∈ gt_finset, gt_min_m' ≤ m' := by
        intro m' hm'
        exact Finset.min_le_of_eq hm' h_gt_min_m'
      have h_lt_finset_lt_set : (lt_finset : Set M) ⊆ lt_set :=
        Set.Finite.subset_toFinset.mp fun ⦃x⦄ a ↦ a
      have h_gt_finset_gt_set : (gt_finset : Set M) ⊆ gt_set :=
        Set.Finite.subset_toFinset.mp fun ⦃x⦄ a ↦ a
      have h_lt_finset_f_source : (lt_finset : Set M) ⊆ f.source := by
        intro m' hm'
        apply h_lt_finset_lt_set at hm'
        unfold lt_set at hm'
        simp only [Set.mem_ofPred_eq] at hm'
        exact hm'.1
      have h_gt_finset_f_source : (gt_finset : Set M) ⊆ f.source := by
        intro m' hm'
        apply h_gt_finset_gt_set at hm'
        unfold gt_set at hm'
        simp only [Set.mem_ofPred_eq] at hm'
        exact hm'.1
      have h_f_source : ∀ m' : M, m' ∈ f.source ↔ (m' ∈ lt_finset ∨ m' ∈ gt_finset) := by
        intro m'
        by_cases h₁ : m' < m
        · constructor
          · intro h₂
            left
            have h₃ : m' ∈ lt_set := by
              unfold lt_set
              simp only [Set.mem_ofPred_eq]
              exact ⟨ h₂, h₁ ⟩
            exact (Set.Finite.mem_toFinset h_lt_set).mpr h₃
          · intro h₂
            obtain h₃ | h₄ := h₂
            · have h₄ : m' ∈ lt_set := Set.mem_sep (h_lt_finset_f_source h₃) h₁
              unfold lt_set at h₄
              simp only [Set.mem_ofPred_eq] at h₄
              exact h₄.1
            · have h₅ : m' ∈ gt_set := Set.mem_sep_iff.mpr (h_gt_finset_gt_set h₄)
              unfold gt_set at h₅
              simp only [Set.mem_ofPred_eq] at h₅
              exact h₅.1
        · constructor
          · intro h₂
            right
            have h₃ : m' ∈ gt_set := by
              unfold gt_set
              simp only [Set.mem_ofPred_eq]
              constructor
              · exact h₂
              · have h₄ : m ≠ m' := Ne.symm (ne_of_mem_of_not_mem h₂ hm')
                grind
            exact (Set.Finite.mem_toFinset h_gt_set).mpr h₃
          · intro h₂
            obtain h₃ | h₄ := h₂
            · have h₄ : m' ∈ lt_set := Set.mem_sep_iff.mpr (h_lt_finset_lt_set h₃)
              unfold lt_set at h₄
              simp only [Set.mem_ofPred_eq] at h₄
              exact h₄.1
            · have h₅ : m' ∈ gt_set := Set.mem_sep_iff.mpr (h_gt_finset_gt_set h₄)
              unfold gt_set at h₅
              simp only [Set.mem_ofPred_eq] at h₅
              exact h₅.1
      have h_m_lt : ∀ m' ∈ lt_finset, m' < m := by
        intro m' hm'
        apply h_lt_finset_lt_set at hm'
        unfold lt_set at hm'
        simp only [Set.mem_ofPred_eq] at hm'
        exact hm'.2
      have h_m_gt : ∀ m' ∈ gt_finset, m < m' := by
        intro m' hm'
        apply h_gt_finset_gt_set at hm'
        unfold gt_set at hm'
        simp only [Set.mem_ofPred_eq] at hm'
        exact hm'.2
      have h_m_lt_max_m' : lt_max_m' < m := by
        have h : lt_max_m' ∈ lt_finset := Finset.mem_of_max h_lt_max_m'
        exact h_m_lt lt_max_m' h
      have h_m_gt_min_m' : m < gt_min_m' := by
        have h : gt_min_m' ∈ gt_finset := Finset.mem_of_min h_gt_min_m'
        exact h_m_gt gt_min_m' h
      have h_lt_max_gt_min_m : lt_max_m' < gt_min_m' := by
        exact Std.lt_trans h_m_lt_max_m' h_m_gt_min_m'
      let lt_max_n' := f.toFun lt_max_m'
      let gt_min_n' := f.toFun gt_min_m'
      have h_lt_max_gt_min_n : lt_max_n' < gt_min_n' := by
        have h₁ : lt_max_m' ∈ f.source := by
          have h : lt_max_m' ∈ lt_finset := Finset.mem_of_max h_lt_max_m'
          exact Set.mem_of_subset_of_mem h_lt_finset_f_source h
        have h₂ : gt_min_m' ∈ f.source := by
          have h : gt_min_m' ∈ gt_finset := Finset.mem_of_min h_gt_min_m'
          exact Set.mem_of_subset_of_mem h_gt_finset_f_source h
        have h₃ : lt_max_m' ≠ gt_min_m' := by exact Std.ne_of_lt h_lt_max_gt_min_m
        have h₄ : lt_max_n' ≠ gt_min_n' := by
          unfold lt_max_n'; unfold gt_min_n'
          by_contra h₅
          apply h₃
          calc
          lt_max_m' = f.invFun (f.toFun lt_max_m') := Eq.symm (f.left_inv' h₁)
          _ = f.invFun (f.toFun gt_min_m') := by rw [h₅]
          _ = gt_min_m' := f.left_inv' h₂
        let a : Fin 2 → M := fun x ↦ if x = 0 then lt_max_m' else gt_min_m'
        have ha : ∀ x, a x ∈ f.source := by
          intro x
          by_cases h : x = 0
          · unfold a
            simp_all
          · unfold a
            simp_all
        have h₅ := f.map_rel' leSymb a ha
        unfold a at h₅
        simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, ne_eq,
          Fin.forall_fin_two, Fin.isValue, relMap_leSymb, ↓reduceIte, one_ne_zero,
          Function.comp_apply, gt_iff_lt]
        have h₆ : lt_max_m' ≤ gt_min_m' := Std.le_of_lt h_lt_max_gt_min_m
        apply h₅.1 at h₆
        unfold lt_max_n'; unfold gt_min_n'
        unfold lt_max_n' at h₄; unfold gt_min_n' at h₄
        exact Std.lt_of_le_of_ne h₆ h₄
      have h_lt_max_gt_min_n' : ∃ n, lt_max_n' < n ∧ n < gt_min_n' :=
        exists_between h_lt_max_gt_min_n
      obtain ⟨ n, hn₁, hn₂ ⟩ := h_lt_max_gt_min_n'
      have h_f_target : ∀ n', n' ∈ f.target ↔
        ((∃ m' ∈ lt_finset, f.toFun m' = n') ∨ (∃ m' ∈ gt_finset, f.toFun m' = n')) := by
          intro n'
          constructor
          · intro hn'
            have hn'₁ := f.map_target' hn'
            apply (h_f_source (f.invFun n')).1 at hn'₁
            obtain hn'₂ | hn'₃ := hn'₁
            · left
              use f.invFun n'
              exact ⟨ hn'₂, f.right_inv' hn' ⟩
            · right
              use f.invFun n'
              exact ⟨ hn'₃, f.right_inv' hn' ⟩
          · intro hn'
            obtain hn'₁ | hn'₂ := hn'
            · obtain ⟨ m', hm'₁, hm'₂ ⟩ := hn'₁
              specialize h_f_source m'
              have hm'₃ : m' ∈ f.source :=
                Set.mem_of_subset_of_mem h_lt_finset_f_source hm'₁
              have hm'₄ := f.map_source' hm'₃
              rw [hm'₂] at hm'₄
              exact hm'₄
            · obtain ⟨ m', hm'₁, hm'₂ ⟩ := hn'₂
              specialize h_f_source m'
              have hm'₃ : m' ∈ f.source :=
                Set.mem_of_subset_of_mem h_gt_finset_f_source hm'₁
              have hm'₄ := f.map_source' hm'₃
              rw [hm'₂] at hm'₄
              exact hm'₄
      have h_n_lt : ∀ m' ∈ lt_finset, f.toFun m' < n := by
        intro m' hm'
        specialize h_lt_max_m'₁ m' hm'
        let a : Fin 2 → M := fun x ↦ if h : x = 0 then m' else lt_max_m'
        have ha : ∀ x, a x ∈ f.source := by
          intro x
          by_cases h : x = 0
          · rw [h]
            unfold a
            simp only [Fin.isValue, ↓reduceDIte]
            apply (h_f_source m').2
            left
            exact hm'
          · unfold a
            simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, not_or,
              Fin.isValue, ↓reduceDIte]
            left
            exact Finset.mem_of_max h_lt_max_m'
        have h := f.map_rel' leSymb a ha
        unfold a at h
        simp only [Fin.isValue, dite_eq_ite, relMap_leSymb, ↓reduceIte, one_ne_zero,
          Function.comp_apply] at h
        apply h.1 at h_lt_max_m'₁
        unfold lt_max_n' at hn₁
        exact Std.lt_of_le_of_lt h_lt_max_m'₁ hn₁
      have h_n_gt : ∀ m' ∈ gt_finset, n < f.toFun m' := by
        intro m' hm'
        specialize h_lt_min_m'₁ m' hm'
        let a : Fin 2 → M := fun x ↦ if h : x = 0 then gt_min_m' else m'
        have ha : ∀ x, a x ∈ f.source := by
          intro x
          by_cases h : x = 0
          · unfold a
            simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, not_or,
              Fin.isValue, ↓reduceDIte]
            right
            exact Finset.mem_of_min h_gt_min_m'
          · unfold a
            simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, not_or,
              Fin.isValue, ↓reduceDIte, or_true]
        have h := f.map_rel' leSymb a ha
        unfold a at h
        simp only [Fin.isValue, dite_eq_ite, relMap_leSymb, ↓reduceIte, one_ne_zero,
          Function.comp_apply] at h
        apply h.1 at h_lt_min_m'₁
        unfold gt_min_n' at hn₂
        exact Std.lt_of_lt_of_le hn₂ h_lt_min_m'₁
      let g : Language.order.PartialIso M N := {
        toFun := fun x ↦ (if h : x = m then n else f.toFun x)
        invFun := fun x ↦ (if h : x = n then m else f.invFun x)
        source := f.source ∪ {m}
        target := f.target ∪ {n}
        map_source' := by
          intro x hx
          by_cases hx₁ : x = m
          · simp_all
          · simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, not_or,
            Set.union_singleton, Set.mem_insert_iff, false_or, ↓reduceDIte]
            right
            obtain hx₂ | hx₃ := hx
            · left
              use x
            · right
              use x
        map_target' := by
          intro x hx
          by_cases hx₁ : x = n
          · simp_all
          · simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, not_or,
            Set.union_singleton, Set.mem_insert_iff, false_or, ↓reduceDIte,
            PartialEquiv.invFun_as_coe]
            obtain hx₂ | hx₃ := hx
            · obtain ⟨ m', hm'₁, hm'₂ ⟩ := hx₂
              have hx₃ : m' = f.invFun x := by
                rw [← hm'₂]
                exact Eq.symm (f.left_inv' (h_lt_finset_f_source hm'₁))
              rw [hx₃] at hm'₁
              right
              left
              exact hm'₁
            · obtain ⟨ m', hm'₁, hm'₂ ⟩ := hx₃
              have hx₄ : m' = f.invFun x := by
                rw [← hm'₂]
                exact Eq.symm (f.left_inv' (h_gt_finset_f_source hm'₁))
              rw [hx₄] at hm'₁
              right
              right
              exact hm'₁
        left_inv' := by
          intro x hx
          by_cases h : x = m
          · simp_all
          · simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype,
            Set.union_singleton, Set.mem_insert_iff, false_or, ↓reduceDIte,
            PartialEquiv.invFun_as_coe, PartialEquiv.left_inv, dite_eq_ite, ite_eq_right_iff]
            intro hx'
            obtain hx₁ | hx₂ := hx
            · specialize h_n_lt x hx₁
              grind
            · specialize h_n_gt x hx₂
              grind
        right_inv' := by
          intro x hx
          by_cases h : x = n
          · simp_all
          · simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, not_or,
            Set.union_singleton, Set.mem_insert_iff, false_or, ↓reduceDIte,
            PartialEquiv.invFun_as_coe, PartialEquiv.right_inv, dite_eq_ite, ite_eq_right_iff]
            intro hx'
            obtain hx₁ | hx₂ := hx
            · obtain ⟨ m', hm'₁, hm'₂ ⟩ := hx₁
              specialize h_f_source m'
              have hm'₃ : m' ∈ lt_finset ∨ m' ∈ gt_finset := by
                left
                exact hm'₁
              apply h_f_source.2 at hm'₃
              rw [← hm'₂] at hx'
              have hm'₄ := f.left_inv' hm'₃
              have hm'₅ : m' = m := by
                rw [← hm'₄, ← hx']
                rfl
              rw [hm'₅] at hm'₁
              specialize h_m_lt m hm'₁
              simp_all
            · obtain ⟨ m', hm'₁, hm'₂ ⟩ := hx₂
              specialize h_f_source m'
              have hm'₃ : m' ∈ lt_finset ∨ m' ∈ gt_finset := by
                right
                exact hm'₁
              apply h_f_source.2 at hm'₃
              rw [← hm'₂] at hx'
              have hm'₄ := f.left_inv' hm'₃
              have hm'₅ : m' = m := by
                rw [← hm'₄, ← hx']
                rfl
              rw [hm'₅] at hm'₁
              specialize h_m_gt m hm'₁
              simp_all
        map_fun' := by
          intros
          trivial
        map_rel' := by
          intro n₁ r a ha
          cases r
          have h : orderRel.le = @leSymb Language.order _ :=
           ((fun a ↦ a) ∘ fun a ↦ a) rfl
          by_cases h₁ : a 0 ∈ f.source
          · by_cases h₂ : a 1 ∈ f.source
            · have h₅ : (fun x ↦ if h : x = m then n else f.toFun x) ∘ a = f.toFun ∘ a := by
                ext x
                simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, not_or,
                  Set.union_singleton, Set.mem_insert_iff, Fin.forall_fin_two, Fin.isValue,
                  and_self, Function.comp_apply, dite_eq_ite,
                  ite_eq_right_iff, or_true]
                intro h₆
                by_cases h₇ : x = 0
                · rw [h₇] at h₆
                  rw [h₆] at h₁
                  simp_all
                · have h₇ : x = 1 := Fin.eq_one_of_ne_zero x h₇
                  rw [h₇] at h₆
                  rw [h₆] at h₂
                  simp_all
              have ha : ∀ x, a x ∈ f.source := by
                intro x
                by_cases h : x = 0
                · rwa [h]
                · have h' : x = 1 := Fin.eq_one_of_ne_zero x h
                  rwa [h']
              constructor
              · intro h₃
                rw [h] at h₃
                have h₄ := f.map_rel' leSymb a ha
                apply h₄.1 at h₃
                rwa [h, h₅]
              · rw [h, h₅]
                intro h₃
                have h₄ := f.map_rel' leSymb a ha
                apply h₄.2 at h₃
                exact h₃
            · rw [h]
              have h₃ : a 1 = m := by specialize ha 1; exact Or.resolve_left ha h₂
              simp only [relMap_leSymb, Fin.isValue, dite_eq_ite, Function.comp_apply]
              rw [← h₃]
              simp only [Fin.isValue, ↓reduceIte]
              rw [h₃]
              have h₄ : a 0 ≠ m := by
                by_contra h₅
                rw [h₅] at h₁
                simp_all
              simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, not_or,
                Set.union_singleton, Set.mem_insert_iff, Fin.forall_fin_two, Fin.isValue, false_or,
                or_self, or_false, and_true, not_false_eq_true, ne_eq, ↓reduceIte]
              obtain ha₁ | ha₂ := ha
              · constructor
                · intro h₅
                  specialize h_n_lt (a 0) ha₁
                  exact Std.le_of_lt h_n_lt
                · intro h₅
                  specialize h_m_lt (a 0) ha₁
                  exact Std.le_of_lt h_m_lt
              · constructor
                · intro h₅
                  specialize h_n_gt (a 0) ha₂
                  exact le_imp_le_of_lt_imp_lt (fun a_1 ↦ h_m_gt (a 0) ha₂) h₅
                · intro h₅
                  specialize h_m_gt (a 0) ha₂
                  exact le_imp_le_of_lt_imp_lt (fun a_1 ↦ h_n_gt (a 0) ha₂) h₅
          · have h₁' : a 0 = m := by specialize ha 0; exact Or.resolve_left ha h₁
            rw [h]
            by_cases h₂ : a 1 ∈ f.source
            · simp_all only [orderedStructure_iff, orderLHom_order, nonempty_subtype, not_or,
              Set.union_singleton, Set.mem_insert_iff, Fin.forall_fin_two, Fin.isValue, or_self,
              or_false, true_and, not_false_eq_true, relMap_leSymb, dite_eq_ite,
              Function.comp_apply, ↓reduceIte, or_true]
              have ha₃ : a 1 ≠ m := by
                by_contra h₃
                rw [h₃] at h₂
                simp_all
              obtain ha₁ | ha₂ := h₂
              · specialize h_n_lt (a 1) ha₁
                specialize h_m_lt (a 1) ha₁
                simp_all only [Fin.isValue, ne_eq, ↓reduceIte]
                constructor
                · intro ha₄
                  exact le_imp_le_of_lt_imp_lt (fun a ↦ h_m_lt) ha₄
                · intro ha₄
                  exact le_imp_le_of_lt_imp_lt (fun a ↦ h_n_lt) ha₄
              · specialize h_n_gt (a 1) ha₂
                specialize h_m_gt (a 1) ha₂
                simp_all only [Fin.isValue, ne_eq, ↓reduceIte]
                constructor
                · intro ha₄
                  exact Std.le_of_lt h_n_gt
                · intro ha₄
                  exact Std.le_of_lt h_m_gt
            · have h₂' : a 1 = m := by specialize ha 1; exact Or.resolve_left ha h₂
              simp_all
      }
      use g
      unfold g
      constructor
      · exact Set.mem_union_right f.source rfl
      · apply (PartialIso.le_def M N f g).2
        grind

theorem dlo_HasQE : HasQE (Language.order.dlo) := by
  apply HasQE_if_BackAndForth_of_finite
  intro M N
  let _ : LE M := {
    le := dlo.le Language.order M
  }
  let _ : LE N := {
    le := dlo.le Language.order N
  }
  let _ : LinearOrder M := {
    le := dlo.le Language.order M
    le_refl := dlo.le_refl Language.order M
    le_trans := dlo.le_trans Language.order M
    lt_iff_le_not_ge := by intros; rfl
    le_antisymm := dlo.le_antisymm Language.order M
    le_total := dlo.le_total Language.order M
    toDecidableLE := Classical.decRel LE.le
    min_def := by intros; rfl
    max_def := by intros; rfl
    compare_eq_compareOfLessAndEq := by intros; rfl
  }
  let _ : LinearOrder N := {
    le := dlo.le Language.order N
    le_refl := dlo.le_refl Language.order N
    le_trans := dlo.le_trans Language.order N
    lt_iff_le_not_ge := by intros; rfl
    le_antisymm := dlo.le_antisymm Language.order N
    le_total := dlo.le_total Language.order N
    toDecidableLE := Classical.decRel LE.le
    min_def := by intros; rfl
    max_def := by intros; rfl
    compare_eq_compareOfLessAndEq := by intros; rfl
  }
  let _ : Language.order.OrderedStructure M := {
    relMap_leSymb := by
      intro v
      have hv₁ : v = fun x ↦ if h : x = 0 then (v 0) else (v 1) := by
        ext x
        grind
      constructor
      · intro hv₂
        rw [hv₁] at hv₂
        finiteness
      · intro hv₂
        rw [hv₁]
        finiteness
  }
  let _ : Language.order.OrderedStructure N := {
    relMap_leSymb := by
      intro v
      have hv₁ : v = fun x ↦ if h : x = 0 then (v 0) else (v 1) := by
        ext x
        grind
      constructor
      · intro hv₂
        rw [hv₁] at hv₂
        finiteness
      · intro hv₂
        rw [hv₁]
        finiteness
  }
  have hM := denselyOrdered_of_dlo Language.order M
  have hN := denselyOrdered_of_dlo Language.order N
  have hM' : Nonempty M := M.nonempty'
  have hN' : Nonempty N := N.nonempty'
  unfold IsBackAndForthSystem
  constructor
  · intro f hf m
    simp only [Set.mem_ofPred_eq] at hf
    let lt_set : Set M := {x | x ∈ f.source ∧ x < m}
    let gt_set : Set M := {x | x ∈ f.source ∧ m < x}
    let lt_finset : Finset M := Set.Finite.toFinset (Finite.Set.finite_sep f.source fun a ↦ a < m)
    let gt_finset : Finset M := Set.Finite.toFinset (Finite.Set.finite_sep f.source (LT.lt m))
    by_cases hm : m ∈ f.source
    · use f
      constructor
      · exact hf
      · constructor
        · exact hm
        · exact PartialIso.le_refl M N f
    · by_cases h₁ : Nonempty lt_finset
      · by_cases h₂ : Nonempty gt_finset
        · sorry
        · sorry
      · by_cases h₃ : Nonempty gt_finset
        · sorry
        · apply Classical.choice at hN'
          let g : Language.order.PartialIso M N := {
            source := {m}
            target := {hN'}
            toFun := fun x ↦ hN'
            invFun := fun x ↦ m
            map_source' := by intros; simp
            map_target' := by intros; simp
            left_inv' := by intros; simp_all
            right_inv' := by intros; simp_all
            map_fun' := by intros; trivial
            map_rel' := by
              intro n r a ha
              unfold Language.order at r
              let r' : orderRel n := r
              cases r'
              have hr : r = @IsOrdered.leSymb Language.order _ := by
                cases r
                exact ((fun a ↦ a) ∘ fun a ↦ a) rfl
              rw [hr]
              simp_all only [nonempty_subtype, not_exists, Set.mem_singleton_iff,
                Fin.forall_fin_two, Fin.isValue, relMap_leSymb, Std.le_refl, Function.comp_apply]
          }
          use g
          constructor
          · simp only [Set.mem_ofPred_eq]
            unfold g
            exact Finite.of_subsingleton
          constructor
          · unfold g
            exact Set.mem_singleton m
          · apply (PartialIso.le_def M N f g).2
            have hf : ¬ ∃ x, x ∈ f.source := by
              by_contra h
              obtain ⟨ x, hx ⟩ := h
              by_cases hx₁ : x < m
              · have hx₁' : x ∈ lt_set := by
                  unfold lt_set
                  sorry
                sorry
              sorry
            sorry
  · sorry
end order
end Language
end FirstOrder

#min_imports
