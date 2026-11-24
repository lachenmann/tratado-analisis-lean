# Referencia TA-LEAN-0010

`SHA256SUMS` identifica las 145 fuentes y configuraciones de la instantánea inicial (las rutas son relativas a la raíz del repositorio). Se conserva el manifiesto original, con 142 fuentes Lean y tres archivos de configuración. `AXIOMAS.txt` contiene las 833 huellas obtenidas por la auditoría directa I03 y cotejadas en I04, una fila por consulta. `<none>` indica ausencia de dependencias axiomáticas.

Audit.lean SHA-256: `D9EFC1B495C02371CFE5B55A8F13F87842B91A772A47A6B779352BAA1357F20C`.

La referencia es histórica e inmutable: no implica que las futuras versiones deban tener exactamente 833 consultas ni las mismas huellas de archivo. Para la primera versión, verificar todas las huellas de fuente; para desarrollo posterior, comprobar las regresiones axiomáticas con el script de CI.
