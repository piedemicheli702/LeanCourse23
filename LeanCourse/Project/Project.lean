import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.ZFC.Basic
import LeanCourse.Common

variable {α : Type*}
namespace ZFSet

#check ∅
#check IsTransitive

def OrdTrans (X : ZFSet) : Prop :=
  X.IsTransitive ∧ ∀ x ∈ X, x.IsTransitive

def HasLeastElement (X : ZFSet) : Prop :=
  ∃ l ∈ X, X ∩ l = ∅

def IsWellOrdered (X : ZFSet) : Prop :=
  ∀ x ⊆ X, x ≠ ∅ → HasLeastElement x

def succ (X : ZFSet) : ZFSet :=
  X ∪ {X}

def IsWellFounded (X : ZFSet) : Prop :=
  ∀ x ⊆ X, x ≠ ∅ → (∃ y ∈ x, x ∩ y = ∅)

lemma empty_ordTrans : OrdTrans ∅ := by {
  unfold OrdTrans
  constructor
  · exact empty_isTransitive
  · intro x hx
    by_contra
    have : x ∉ ∅ := by apply not_mem_empty
    contradiction
}

lemma succ_ordTrans {X : ZFSet} (h : OrdTrans X) : OrdTrans (succ X) := by {
  unfold OrdTrans IsTransitive
  constructor
  · intro y hy z hz
    apply ZFSet.mem_union.2
    apply ZFSet.mem_union.1 at hy
    rcases hy with hy_1 | hy_2
    · left
      rw [OrdTrans] at h
      apply h.1 at hy_1
      exact hy_1 hz
    · left
      have : y = X := by exact mem_singleton.mp hy_2
      rwa [this] at hz
  · intro x hx y hy
    apply ZFSet.mem_union.1 at hx
    rcases hx with hx_1 | hx_2
    · have : IsTransitive x := by
        apply h.2 at hx_1
        assumption
      exact this y hy
    · have : x = X := by exact mem_singleton.mp hx_2
      rw [this] at hy
      rw [this]
      apply h.1 at hy
      assumption
}

lemma succ_neq_empty {X : ZFSet} : succ X ≠ ∅ := by {
  rw [succ]
  rw [Ne]
  rw [eq_empty]
  push_neg
  use X
  rw [mem_union]
  right
  exact mem_singleton.mpr rfl
}

#check ZFSet.regularity

def SuccOrd (X : ZFSet) : Prop :=
  OrdTrans X ∧ ∃ Y, (OrdTrans Y ∧ succ Y = X)

def LimOrd (X : ZFSet) : Prop :=
  OrdTrans X ∧ (¬ ∃ Y, (OrdTrans Y ∧ succ Y = X)) ∧ X ≠ ∅

lemma ordTrans_empty_or_succ_or_lim {X : ZFSet} (hX : OrdTrans X) : X = ∅ ∨ SuccOrd X ∨ LimOrd X := by {
  have hXdup : OrdTrans X := hX
  by_contra hnX
  push_neg at hnX
  rcases hnX with ⟨hXnem, hXnsucc, hXnlim⟩
  unfold SuccOrd at hXnsucc
  push_neg at hXnsucc
  unfold LimOrd at hXnlim
  push_neg at hXnlim
  apply hXnsucc at hX
  apply hXnlim at hX
  contradiction
  exact hXdup
}

#check ZFSet.inductionOn

#check PSet.ofNat

theorem ordTrans_wellordered {X : ZFSet} {hX : OrdTrans X} : IsWellOrdered X := by {
  rw [IsWellOrdered]
  intro x hx hneq
  rw [HasLeastElement]
  apply regularity
  assumption
}

theorem ordTrans_inductionOn {p : ZFSet → Prop} (X : ZFSet) (hX : OrdTrans X) : p ∅ → (∀ Z, OrdTrans Z → p Z → p (succ Z)) → (∀ Y, Y ⊆ X ∧ LimOrd Y → (∀ Z ∈ Y, p Z) → p Y) → p X := by {
  intro hempty hsucc hlim
  sorry
}

lemma eq_empty_of_subset {X : ZFSet} : X ⊆ ∅ → X = ∅ := by {
  intro h
  rw [ZFSet.subset_def] at h
  rw [eq_empty]
  intro y hy
  apply h at hy
  apply not_mem_empty at hy
  assumption
}

lemma union_singleton_of_mem {X Y : ZFSet} (h : X ∪ {X} = Y) : X ∈ Y := by {
  rw [←h]
  apply mem_union.2
  right
  exact mem_singleton.mpr rfl
}

theorem ordTrans_mem_of_subset {X₀ X₁ : ZFSet} (h : OrdTrans X₀) (h₀ : OrdTrans X₁) (h₁ : X₁ ⊆ X₀) (h₂ : X₀ ≠ ∅): X₁ ∈ X₀ := by {
  by_contra hcon
  sorry
}

/-theorem ordTrans_mem_of_subset {X₀ X₁ : ZFSet} (h : OrdTrans X₀) (h₁ : X₁ ⊆ X₀) (h₂ : X₀ ≠ ∅) : X₁ ∈ X₀ := by {
  induction X₀ using inductionOn
  case h x hx
  · apply ordTrans_empty_or_succ_or_lim at h
    rcases h with hem | hsucc | hlim
    · by_contra h
      contradiction
    · rw [SuccOrd] at hsucc
      obtain ⟨z, hz⟩ := hsucc.2
      rw [OrdTrans] at hsucc
      rw [IsTransitive] at hsucc
      have : z ∈ x := by apply union_singleton_of_mem hz.2
      apply hx at this
      have hzord : OrdTrans z := hz.1
      apply this at hzord

    · rw [LimOrd] at hlim
      sorry
}-/

lemma ordTrans_pair_union {X Y : ZFSet} (hX : OrdTrans X) (hY : OrdTrans Y) : OrdTrans (X ∪ Y) := by {
  rw [OrdTrans]
  constructor
  · rw [IsTransitive]
    rw [OrdTrans] at hX hY
    intro y hy y₀ hy₀
    have hyp : y ∈ X ∨ y ∈ Y := by exact mem_union.mp hy
    rcases hyp with h | h
    · apply hX.1 at h
      apply h at hy₀
      rw [mem_union]
      left
      assumption
    · apply hY.1 at h
      apply h at hy₀
      rw [mem_union]
      right
      assumption
  · intro x hx
    rw [IsTransitive]
    intro y hy
    rw [OrdTrans] at hX hY
    have hyp : x ∈ X ∨ x ∈ Y := by exact mem_union.mp hx
    rcases hyp with h | h
    · apply hX.2 <;> assumption
    · apply hY.2 <;> assumption
}

lemma ordTrans_pair_inter {X Y : ZFSet} (hX : OrdTrans X) (hY : OrdTrans Y) : OrdTrans (X ∩ Y) := by {
  rw [OrdTrans]
  constructor
  · rw [OrdTrans] at hX hY
    rw [IsTransitive]
    rw [IsTransitive] at hX hY
    intro y hy
    have hyp1 : y ⊆ X := by {
      apply hX.1
      rw [mem_inter] at hy
      exact hy.1
    }
    have hyp2 : y ⊆ Y := by {
      apply hY.1
      rw [mem_inter] at hy
      exact hy.2
    }
    intro z hz
    have hz1 : z ∈ X := by exact hyp1 hz
    have hz2 : z ∈ Y := by exact hyp2 hz
    apply mem_inter.2
    constructor <;> assumption
  · intro x hx
    rw [OrdTrans] at hX hY
    have : x ∈ X := by {
      rw [mem_inter] at hx
      exact hx.1
    }
    apply hX.2 at this
    assumption
}

lemma subset_inter_left {X Y : ZFSet} : (X ∩ Y) ⊆ X := by {
  intro z hz
  rw [mem_inter] at hz
  exact hz.1
}

lemma subset_inter_right {X Y :ZFSet} : (X ∩ Y) ⊆ Y := by {
  intro z hz
  rw [mem_inter] at hz
  exact hz.2
}

theorem ordTrans_mem_or_eq_or_mem {X Y : ZFSet} (h : X ≠ ∅) (h1 : Y ≠ ∅): OrdTrans X → OrdTrans Y → X ≠ Y → (X ∈ Y ∨ Y ∈ X) := by {
  intro hX hY
  by_contra hyp
  push_neg at hyp
  have h1 : X ∩ Y ∈ X := by {
    have : OrdTrans (X ∩ Y) := by exact ordTrans_pair_inter hX hY
    have hyp₀ : (X ∩ Y) ⊆ X := by exact subset_inter_left
    apply ordTrans_mem_of_subset
    constructor
    · apply hX.1
    · apply hX.2
    · exact this
    · assumption
    · assumption
  }
  have h2 : X ∩ Y ∈ Y := by {
    have : OrdTrans (X ∩ Y) := by exact ordTrans_pair_inter hX hY
    have hyp₀ : (X ∩ Y) ⊆ Y := by exact subset_inter_right
    apply ordTrans_mem_of_subset
    constructor
    . apply hY.1
    · apply hY.2
    · exact this
    · assumption
    · assumption
  }
  have h3 : X ∩ Y ∈ X ∩ Y := by {
    apply mem_inter.2
    constructor <;> assumption
  }
  have : X ∩ Y ∉ X ∩ Y := by apply mem_irrefl
  contradiction
}

lemma succ_neq_succ {X Y :ZFSet} {hX : OrdTrans X} {hY : OrdTrans Y} {hnem : X ≠ ∅ ∧ Y ≠ ∅}: X ≠ Y → succ X ≠ succ Y := by {
  intro hneq
  have hneqcopy : X ≠ Y := by exact hneq
  apply ordTrans_mem_or_eq_or_mem at hneq
  rotate_left
  · exact hnem.1
  · exact hnem.2
  · assumption
  · assumption
  · rcases hneq with h₀ | h₀
    · by_contra h
      rw [succ] at h
      rw [succ] at h
      rw [ext_iff] at h
      have hyp' : Y ∈ Y ∪ {Y} := by exact union_singleton_of_mem rfl
      have : Y ∈ X ∪ {X} := by {
        rw [h]
        assumption
      }
      rw [mem_union] at this
      rcases this with h₁ | h₁
      · apply mem_asymm at h₁
        contradiction
      · rw [mem_singleton] at h₁
        exact hneqcopy (id h₁.symm)
    · by_contra h
      rw [succ] at h
      rw [succ] at h
      rw [ext_iff] at h
      have hyp : X ∈ X ∪ {X} := by exact union_singleton_of_mem rfl
      have : X ∈ Y ∪ {Y} := by {
        rw [←h]
        assumption
      }
      rw [mem_union] at this
      rcases this with h₁ | h₁
      · apply mem_asymm at h₁
        contradiction
      · rw [mem_singleton] at h₁
        contradiction
}

lemma succ_subset_of_mem {X Y : ZFSet} {hX : OrdTrans X} {hY : OrdTrans Y} : X ∈ Y → succ X ⊆ Y := by {
  intro hmem
  have : X ≠ Y := by {
    by_contra h
    rw [h] at hmem
    apply mem_irrefl at hmem
    assumption
  }
  intro z hz
  rw [succ] at hz
  rw [mem_union] at hz
  rw [OrdTrans] at hY
  rcases hz with hz | hz
  · apply hY.1 at hmem
    exact hmem hz
  · have : z = X := by exact mem_singleton.mp hz
    rw [this]
    assumption
}

lemma succ_mem_of_limord_mem {X Y : ZFSet} {hX : OrdTrans X} {hY : OrdTrans Y} {hYlim : LimOrd Y} : X ∈ Y → succ X ∈ Y := by {
  intro hmem
  have : succ X ≠ Y := by {
    rw [LimOrd] at hYlim
    have : ¬∃ X, OrdTrans X ∧ succ X = Y := by {
      apply hYlim.2.1
    }
    by_contra h
    push_neg at this
    apply this at h <;> assumption
  }
  apply ordTrans_mem_or_eq_or_mem at this
  · rcases this with h | h
    · assumption
    · have : False := by {
        rw [succ] at h
        rw [mem_union] at h
        rcases h with h | h
        · apply mem_asymm at h
          contradiction
        · rw [mem_singleton] at h
          rw [h] at hmem
          apply mem_irrefl at hmem
          assumption
      }
      exfalso
      assumption
  · exact succ_neq_empty
  · rw [LimOrd] at hYlim
    apply hYlim.2.2
  · exact succ_ordTrans hX
  · assumption
}

lemma ordTrans_sUnion {X : ZFSet} (hX : ∀ x ∈ X, OrdTrans x) : OrdTrans (⋃₀ X) := by {
  rw [OrdTrans]
  constructor
  · rw [IsTransitive]
    intro y hy
    rw [mem_sUnion] at hy
    intro a ha
    obtain ⟨z, hz1, hz2⟩ := hy
    have : a ∈ z := by {
      apply hX at hz1
      rw [OrdTrans] at hz1
      rw [IsTransitive] at hz1
      have : y ⊆ z := by {
        apply hz1.1 at hz2
        assumption
      }
      exact this ha
    }
    apply mem_sUnion_of_mem this
    assumption
  · intro x hx
    rw [IsTransitive]
    intro y hy z hz
    rw [mem_sUnion] at hx
    obtain ⟨a, ha1, ha2⟩ := hx
    apply hX at ha1
    rw [OrdTrans] at ha1
    apply ha1.2 at ha2
    rw [IsTransitive] at ha2
    have : y ⊆ x := by {
      exact ha2 y hy
    }
    exact ha2 y hy hz
}

lemma ordTrans_of_mem {X Y : ZFSet} {hX : OrdTrans X} : Y ∈ X → OrdTrans Y := by {
  intro hY
  rw [OrdTrans]
  constructor
  · rw [IsTransitive]
    intro y hy z hz
    rw [OrdTrans] at hX
    apply hX.2 at hY
    apply hY at hy
    exact hy hz
  · intro x hx
    rw [IsTransitive]
    intro y hy z hz
    apply hX.1 at hx
    apply hX.2 at hx
    apply hx at hy
    exact hy hz
    exact hY
}

lemma sUnion_ordTrans_subset {X : ZFSet} {hX : OrdTrans X} {hnem : X ≠ ∅} : (⋃₀ X : ZFSet) ⊆ X := by {
  intro z hz
  have : OrdTrans (⋃₀ X) := by {
    apply ordTrans_sUnion
    intro x hx
    apply ordTrans_of_mem hx
    assumption
  }
  have h : OrdTrans z := by {
    apply ordTrans_of_mem hz
    exact this
  }
  induction z using inductionOn
  case h z hz'
  sorry
}

theorem sUnion_lim_eq_lim {X : ZFSet} {hX : LimOrd X} : X = (⋃₀ X : ZFSet) := by {
  sorry
}

lemma ordTrans_sInter {X : ZFSet} (hX : ∀ x ∈ X, OrdTrans x) (hXnem : ZFSet.Nonempty X) : OrdTrans (⋂₀ X) := by {
  rw [OrdTrans]
  constructor
  · rw [IsTransitive]
    intro y hy z hz
    rw [mem_sInter]
    · intro a ha
      have hyp₀ : y ∈ a := by {
        exact mem_of_mem_sInter hy ha
      }
      have hyp₁ : OrdTrans a := by exact hX a ha
      have hyp₂ : y ⊆ a  := by {
        rw [OrdTrans] at hyp₁
        rw [IsTransitive] at hyp₁
        apply hyp₁.1
        assumption
      }
      exact hyp₂ hz
    · exact hXnem
  · intro x hx
    rw [IsTransitive]
    intro y hy a ha
    have : ∃ z ∈ X, x ∈ z := by {
      have : ∃ w, w ∈ X := by exact hXnem
      obtain ⟨w, hw⟩ := this
      use w
      constructor
      · assumption
      · exact mem_of_mem_sInter hx hw
    }
    obtain ⟨z, hz1, hz2⟩ := this
    apply hX at hz1
    rw [OrdTrans] at hz1
    apply hz1.2 at hz2
    exact hz2 y hy ha
}

lemma ordTrans_iff_ordTrans_and_trans {X : ZFSet} : OrdTrans X ↔ ((∀ x ∈ X, OrdTrans x) ∧ IsTransitive X) := by {
  constructor
  · intro hX
    constructor
    · intro x hx
      apply ordTrans_of_mem hx
      assumption
    · exact hX.1
  · intro h
    rw [OrdTrans]
    constructor
    · exact h.2
    · intro x hx
      apply h.1 at hx
      exact hx.1
}

theorem burali_forti : ¬∃ (X : ZFSet), ∀ x, OrdTrans x ↔ x ∈ X := by {
  by_contra h
  obtain ⟨X, hX⟩ := h
  have htrans : IsTransitive X := by {
    intro x hx z hz
    have : OrdTrans x := by {
      rw [hX]
      assumption
    }
    have : OrdTrans z := by {
      apply ordTrans_of_mem hz
      assumption
    }
    rw [hX] at this
    assumption
  }
  have : OrdTrans X := by {
    apply ordTrans_iff_ordTrans_and_trans.2
    constructor
    · intro x hx
      rw [hX]
      assumption
    · assumption
  }
  have : X ∈ X := by {
    rw [← hX]
    assumption
  }
  apply mem_irrefl X
  assumption
}

theorem ordTrans_ofNat {n : ℕ} : OrdTrans (ZFSet.mk (PSet.ofNat n)) := by {
  rw [OrdTrans]
  constructor
  · rw [IsTransitive]
    intro x hx
    induction n with
    | zero => have : PSet.ofNat 0 = ∅ := by {
                       exact rfl
                     }
              rw [this]
              rw [this] at hx
              have : mk ∅ = ∅ := by {
                      rfl
              }
              rw [this]
              rw [this] at hx
              by_contra hyp
              have : x ∉ ∅ := by {
                     apply not_mem_empty
              }
              contradiction
    | succ n ih => have : PSet.ofNat (n + 1) = PSet.insert (PSet.ofNat n) (PSet.ofNat n) := by {
                            rfl
    }
                   rw [this] at hx
                   sorry
  · intro x hx
    rw [IsTransitive]
    intro y hy
    induction n with
    | zero => by_contra hyp
              have : PSet.ofNat 0 = ∅ := by rfl
              rw [this] at hx
              have : mk ∅ = ∅ := by rfl
              rw [this] at hx
              have : x ∉ ∅ := by {
                apply not_mem_empty
              }
              contradiction
    | succ n ih =>  have hsub : PSet.ofNat n ⊆ PSet.ofNat (n + 1) := by {
                      have : PSet.ofNat (n + 1) = PSet.insert (PSet.ofNat n) (PSet.ofNat n) := by rfl
                      rw [this]
                      intro a
                      sorry
                    }
                    have : x ∈ mk (PSet.ofNat n) := by {
                     sorry
                    }
                    apply ih at this
                    assumption
}

#check OrdTrans

#check ZFSet.IsWellOrdered

def OrdVonNeumann (X : ZFSet) : Prop :=
  IsWellOrdered X ∧ ∀ x ∈ X, x ⊆ X

#check OrdVonNeumann

lemma nametbd {X : ZFSet} {hX : OrdVonNeumann X} : x ∈ X → y ∈ X → x ≠ y → (x ∈ y ∨ y ∈ x) := by {
  intro hx hy hneq
  rw [OrdVonNeumann] at hX
  have : {x, y} ⊆ X := by {
    intro z hz
    rw [mem_pair] at hz
    rcases hz with hz | hz
    · rw [hz]
      assumption
    · rw [hz]
      assumption
  }
  apply hX.1 at this
  have hyp : {x, y} ≠ ∅ := by {
    rw [Ne]
    rw [eq_empty]
    push_neg
    use x
    refine mem_insert x {y}
  }
  sorry
}

theorem ord_Trans_iff_VonNeumann {X : ZFSet} : OrdTrans X ↔ OrdVonNeumann X := by {
  constructor
  · intro hX
    constructor
    · rw [IsWellOrdered]
      intro x hx hneq
      apply regularity
      assumption
    · intro x hx
      unfold OrdTrans at hX
      unfold IsTransitive at hX
      apply hX.1 at hx
      exact hx
  · intro hX
    constructor
    · rw [OrdVonNeumann] at hX
      rw [IsTransitive]
      exact hX.2
    · intro x hx
      rw [IsTransitive]
      rw [OrdVonNeumann] at hX
      intro y hy
      intro z hz
      have h₀: y ∈ X := by {
        apply hX.2 at hx
        exact hx hy
      }
      have h₁ : z ∈ X := by {
        apply hX.2 at h₀
        exact h₀ hz
      }
      rw [IsWellOrdered] at hX
      sorry
}
