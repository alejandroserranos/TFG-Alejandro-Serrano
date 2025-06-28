# TFG-Alejandro-Serrano
Repositorio donde se almacenan los códigos desarrollados y utilizados a lo largo del Trabajo de Fin de Grado titulado:
"Grandes Modelos de Lenguaje para la Verificación Formal de Programas".

ESTRUCTURA DEL REPOSITORIO:
Este repositorio se estructura de la siguiente forma:
1. Ejemplo inicial.
2. Búsqueda Binaria.
    - Búsqueda Binaria
    - Búsqueda Binaria Iterativo
3. Algoritmos de Ordenación.
    - MergeSort
    - QuickSort
4. Recursión sobre Árboles Binarios.

CONTENIDO:
En cada uno de los apartados se incluyen archivos .dfy con:
  - El código inicial sin especificaciones (funcional pero no verificado).
  - Varias versiones especificadas mediante el uso de ChatGPT, generadas con los distintos prompts. Estas versiones se nombran como 'Pn', donde n ∈ {1,2,3,4} representa el número del prompt utilizado (véase sección 4.2 de la memoria).

Si el nombre de un archivo contiene la palabra cambiado, significa que ha sido modificado o corregido manualmente respecto a la salida generada por el modelo.

Algunos de estos archivos se encuentran en las carpetas 'Pruebas con otros Prompts', estos archivos no se incluyen explícitamente en la memoria pero sí aparecen en la tabla comparativa de los prompts.

Además de los archivos en Dafny, se incluyen dos scripts en Python generados automáticamente con ChatGPT:
  - BinarySearchItP1.py: versión iterativa de búsqueda binaria generada a partir del Prompt 1.
  - SumABP1.py: función de suma de los elementos de un Árbol Binario con especificación, también generada con Prompt 1.

COMO USAR LOS CÓDIGOS:
Para trabajar con los archivos .dfy se ha utilizado Visual Studio Code, junto con la extensión oficial de Dafny (versión recomendada: v3.4.4 o superior (incluye el verificador Z3)).
Una vez instalada la extensión, basta con abrir un archivo .dfy en VS Code y Dafny verificará automáticamente el código al guardarlo (Ctrl+S).
