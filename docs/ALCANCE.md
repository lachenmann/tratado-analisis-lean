# Alcance y límites de v0.1.0

Base: TA-LEAN-0010, cierre canónico del 24-11-2026. Se exportan las 142 fuentes Lean y tres configuraciones certificadas, sin reescribir las demostraciones, junto con la referencia de 833 huellas de auditoría. La instantánea original de fuentes y configuración tiene 1.046.594 bytes.

## Niveles de certificación

- `lean-check`: contraste de resultados con estructuras estándar; no equivale por sí mismo a un cotejo fundacional con el manuscrito.
- `lean-structural`: desarrollo en estructuras propias del lenguaje de tipos.
- `lean-foundational-bridge`: puente hacia la infraestructura conjuntista.
- `lean-foundational`: representación de los objetos conjuntistas del tratado y sus operaciones.

Una declaración elaborada no equivale necesariamente a una demostración humana traducida paso a paso. En particular, TA-THM-00057 y TA-COR-00028 tienen una prueba formal alternativa de Pell. Véase [correspondencia](CORRESPONDENCIA.md).

## Dependencias axiomáticas

| Huella | Consultas |
|---|---:|
| `propext, Quot.sound` | 757 |
| `Classical.choice, propext, Quot.sound` | 65 |
| `Quot.sound` | 4 |
| `propext` | 3 |
| Sin axiomas | 4 |
| Total | 833 |

Las 71 consultas incorporadas en TA-LEAN-0010 no añaden dependencias de `Classical.choice`. Cero `sorryAx` entre las consultas auditadas. El tercero excluido, cuando se necesita en los nuevos resultados, se suministra explícitamente como `em : ∀ p : Prop, p ∨ ¬p`. Esto no certifica constructividad integral. Las definiciones auxiliares `N05A1.pellPair` y `QuadraticCofinality0010` están elaboradas y consultadas mediante `#check`, pero no poseen consulta axiomática individual en esa auditoría.

## Trabajo pendiente

- Cotejo semántico de la capa `lean-check` del capítulo 0 y formalización pendiente de TA-PRO-00427, TA-PRO-00428 y TA-COR-00139.
- Interfaz exclusivamente de grafo de las incrustaciones.
- Unicidad e isomorfismos de completaciones y puente hacia `ℝ` de Mathlib.
- Sucesiones racionales, construcción de Cauchy y desarrollo posterior del análisis.

El alcance no se extiende a esos resultados por publicar esta versión.

## Evidencia

La compilación histórica I03 de Windows (Lean 4.32.1) tuvo 896 trabajos con caché existente y se cotejó independientemente con las fuentes exportadas. El cierre posterior fue documental: no ejecutó un nuevo kernel. La referencia de axiomas de esta edición se conserva en `certificates/TA-LEAN-0010/AXIOMAS.txt`. Los logs internos, identificadores de almacenamiento y respaldos privados no se incluyen.
