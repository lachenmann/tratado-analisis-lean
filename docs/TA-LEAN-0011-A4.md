# TA-LEAN-0011 — A4: convergencia racional (§8.3)

Base: A3 certificado por [CI #16](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45453380018), commit 431486baa34a399312e058d5e79424f6cbc980f1. 912 trabajos; 40/40 consultas con propext y Quot.sound; 1074 huellas acumuladas; clausura de 42 módulos locales independiente de Dedekind. Se fijan A3_AXIOMAS.txt y los cuatro blobs Lean de A3.

Fuente: capítulo 8 v1.1.0, §§8.3.1–8.3.5. Candidato de cinco nodos:
- TA-DEF-00109: RationalConverges y RationalConvergent, precisiones y límites racionales, índices naturales conjuntistas. IsConvergenceModulus, módulo mínimo canónico por Separación con em explícito.
- TA-NOT-00019: notación local ⟶ℚ y puente definicional.
- TA-PRO-00111 (TA-PRF-00223): equivalencias de las tres formulaciones, mismo índice N.
- TA-PRO-00112 (TA-PRF-00224): convergencia de constantes con N=0.
- TA-THM-00058 (TA-PRF-00225): unicidad del límite por tricotomía proposicional de Q, mitad positiva, totalidad de N y desigualdad triangular.

Decisiones de implementación: la totalidad y minimalidad naturales se transportan mediante códigos Nat locales para conservar la independencia de los módulos abstractos posteriores a Q. La prueba de mínimo requiere em como argumento explícito; no hay función global de selección de índices, ni se afirma computabilidad del módulo mínimo. La unicidad del límite no necesita em; la tricotomía proposicional certificada no se presenta como un decisor global de ZFSet. Se reutiliza la distancia racional de A3 y la división racional preexistente.

39 declaraciones auditadas, además de 1074 huellas históricas. Se conserva cada fuente Lean anterior, y se amplía el control de importaciones locales. Candidato pendiente de CI. La construcción del cociente se reserva a capítulos posteriores. Registro canónico de la bóveda pendiente de actualización.
