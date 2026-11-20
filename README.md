# nrs3-golab

Lean 4 / Mathlib (v4.35.0). `lake build`: 0 `sorry`, axiomas estándar (`propext`, `Classical.choice`, `Quot.sound`).

## Contenido

| Archivo | Resultado principal |
|---|---|
| [`NRS3Golab/Hexagon.lean`](NRS3Golab/Hexagon.lean) | Gołąb, casos extremos: la norma hexagonal `max(|x|, |y|, |x−y|)` tiene como círculo unitario exactamente un hexágono de perímetro 6, así que `π_hex = 3` (`hexPi_eq_three`). La norma del cuadrado da `π_sq = 4`. `golab_extremes`: `3 = π_hex < π < π_sq = 4` |
| [`NRS3Golab/InnerProductPi.lean`](NRS3Golab/InnerProductPi.lean) | Producto interno → Cauchy–Schwarz → π exacto: ángulo bien definido, ángulo llano `= π`, suma de ángulos del triángulo `= π`, cuerda `= 2 sin(θ/2)`, perímetros de Arquimedes `2n sin(π/n) → 2π` (`tendsto_archimedesPerimeter`) |
| [`NRS3Golab/OrbitStability.lean`](NRS3Golab/OrbitStability.lean) | Ehrenfest (1917): en `d` ejes espaciales `G'(r₀) = (d − 4) k r₀^{−d}`; órbitas circulares estables si y solo si `d < 4`; entre `d ≥ 3` solo `d = 3`, espaciotiempo `d + 1 = 4` (`stable_iff_spacetime_four`) |
| [`NRS3Golab/QuantumStability.lean`](NRS3Golab/QuantumStability.lean) | En el Hilbert `ℂ^d` todo operador cumple `−‖H‖‖ψ‖² ≤ Re⟪ψ, Hψ⟫` para toda `d` (`re_inner_ge_of_Cd`); las tres matrices de Pauli anticonmutan; en el continuo, energía de dilatación acotada para todo acoplamiento si y solo si `n = 3` (`bddBelow_all_couplings_iff`) |

## Alcance

- Gołąb general (`6 ≤ perímetro ≤ 8` para toda norma) no está demostrado; sí sus dos casos de igualdad.
- La circunferencia euclidiana se toma como límite de los polígonos inscritos (Arquimedes).
- `OrbitStability` es mecánica newtoniana con la ley de Gauss en `d` dimensiones.
- En `QuantumStability`, parte 3, la cota para `n = 3` es sobre la órbita de dilatación; la cota sobre todos los estados requiere la desigualdad de Hardy.

## Compilar

```bash
lake exe cache get
lake build
```

## Licencia

NRS Noncommercial License 1.0.0, ver [`LICENSE`](LICENSE).
