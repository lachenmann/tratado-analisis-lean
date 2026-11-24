# Certificado de consolidación v0.1.1

Candidato basado en el commit `d3007dbde0460668c76e979f5072ec9d11e4e0c9` (v0.1.0). La etiqueta y los archivos históricos de TA-LEAN-0010 permanecen intactos.

- `SHA256SUMS`: fuentes Lean y configuraciones de esta versión, incluida la prueba de API, sin incluir el propio manifiesto.
- `API_ALIASES.tsv`: 24 aliases y sus declaraciones de origen.
- `tests/PublicAPI.lean`: 39 firmas históricas de N05, 24 consultas de aliases y una del puente de positividad.
- `scripts/check_public_api.py`: exige igualdad exacta de las 833 huellas históricas y de cada alias con su origen. El puente nuevo solo puede depender de propext y Quot.sound o de un subconjunto.

No se anuncia PASS de esta versión hasta la conclusión del CI. El certificado de v0.1.0 sigue siendo la referencia histórica; los SHA de código depurado no deben confundirse con los de la instantánea original.
