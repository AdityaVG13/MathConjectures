import GaugeCoordinateRing

namespace PermanentGauge.Coordinates

/-- The actual lifted maps fix each unit-pivot coordinate. -/
theorem forwardMap_units (k : Fin 9) :
    Units.map forwardMap.toMonoidHom (units k) = units k := by
  apply Units.ext
  change forwardMap (units k : A) = (units k : A)
  rw [units_value, forwardMap_matrix]
  simpa using forwardImage_pivot k

theorem inverseMap_units (k : Fin 9) :
    Units.map inverseMap.toMonoidHom (units k) = units k := by
  apply Units.ext
  change inverseMap (units k : A) = (units k : A)
  rw [units_value, inverseMap_matrix]
  simpa using inverseImage_pivot k

theorem map_rowFactor (f : A →+* A)
    (h : ∀ k, Units.map f.toMonoidHom (units k) = units k) (i : Fin 5) :
    Units.map f.toMonoidHom (rowFactor units i) = rowFactor units i := by
  have h' : ∀ k, Units.map (f : A →* A) (units k) = units k := h
  fin_cases i <;> simp [rowFactor, h']

theorem map_colFactor (f : A →+* A)
    (h : ∀ k, Units.map f.toMonoidHom (units k) = units k) (i : Fin 5) :
    Units.map f.toMonoidHom (colFactor units i) = colFactor units i := by
  have h' : ∀ k, Units.map (f : A →* A) (units k) = units k := h
  fin_cases i <;> simp [colFactor, h']

theorem map_normalize (f : A →+* A)
    (h : ∀ k, Units.map f.toMonoidHom (units k) = units k)
    (M : Matrix (Fin 5) (Fin 5) A) (i j : Fin 5) :
    f (normalize units M i j) = normalize units (fun i j => f (M i j)) i j := by
  have hr := congrArg (fun v : Aˣ => (v : A)) (map_rowFactor f h i)
  have hc := congrArg (fun v : Aˣ => (v : A)) (map_colFactor f h j)
  change f (rowFactor units i : A) = (rowFactor units i : A) at hr
  change f (colFactor units j : A) = (colFactor units j : A) at hc
  simp [normalize, scaleMatrix, hr, hc]

theorem map_reconstruct (f : A →+* A)
    (h : ∀ k, Units.map f.toMonoidHom (units k) = units k)
    (M : Matrix (Fin 5) (Fin 5) A) (i j : Fin 5) :
    f (reconstruct units M i j) = reconstruct units (fun i j => f (M i j)) i j := by
  have hr : Units.map f.toMonoidHom ((rowFactor units i)⁻¹) = (rowFactor units i)⁻¹ := by
    rw [map_inv, map_rowFactor f h i]
  have hc : Units.map f.toMonoidHom ((colFactor units j)⁻¹) = (colFactor units j)⁻¹ := by
    rw [map_inv, map_colFactor f h j]
  have hr' := congrArg (fun v : Aˣ => (v : A)) hr
  have hc' := congrArg (fun v : Aˣ => (v : A)) hc
  change f (((rowFactor units i)⁻¹ : Aˣ) : A) = _ at hr'
  change f (((colFactor units j)⁻¹ : Aˣ) : A) = _ at hc'
  simp [reconstruct, scaleMatrix, hr', hc']

theorem map_clearPivots (f : A →+* A) (M : Matrix (Fin 5) (Fin 5) A) (i j : Fin 5) :
    f (clearPivots M i j) = clearPivots (fun i j => f (M i j)) i j := by
  classical
  by_cases h : IsPivot (i,j) <;> simp [clearPivots, h]

#print axioms forwardMap_units
#print axioms map_reconstruct
end PermanentGauge.Coordinates
