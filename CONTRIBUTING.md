# Contribuir

Las correcciones de pruebas, observaciones fundacionales y reportes de discrepancias entre el manuscrito y Lean son bienvenidos mediante issues y pull requests.

1. Identificar el resultado mediante su `TA-...` y la declaración Lean completa.
2. Conservar las hipótesis, el universo y la representación de los objetos; documentar las pruebas alternativas.
3. Evitar `sorry`, `admit`, axiomas añadidos y nuevas dependencias de `Classical.choice` no justificadas. Si se requiere lógica clásica, explicitar su uso y el alcance del resultado.
4. Mantener las versiones fijadas salvo una actualización deliberada y auditada. Ejecutar `lake build` y la auditoría; actualizar la correspondencia si procede.
5. No subir manuscritos privados, respaldos, cachés, datos personales, credenciales ni logs con rutas de usuario. Atribuir cualquier fragmento externo y respetar sus condiciones de licencia. Las contribuciones destinadas al código propio se ofrecen bajo la licencia Apache 2.0 del repositorio.

La referencia histórica de TA-LEAN-0010 es inmutable en desarrollo ordinario. La comprobación de CI protege las huellas antiguas y permite nuevas consultas con axiomas autorizados; un cambio deliberado de una huella antigua requiere revisión explícita de la política y un nuevo checkpoint, sin borrar la evidencia histórica.
