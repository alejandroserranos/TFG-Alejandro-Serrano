# TFG-Alejandro-Serrano
Repositorio donde se almacenan los códigos desarrollados y utilizados a lo largo del Trabajo de Fin de Grado titulado:
"Grandes Modelos de Lenguaje para la Verificación Formal de Programas".

ESTRUCTURA DEL REPOSITORIO:

Este repositorio se estructura de la siguiente forma:
- Códigos TFG
  - 2.2. Ejemplo Dafny
  - 4.1. Ejemplos Iniciales
    - 4.1.1. Verificación Simple
    - 4.1.2. División entera (versión iterativa)
    - 4.1.3. División entera (versión recursiva)
    - 4.1.4. Logaritmo entero
 - 4.3. Búsqueda Binaria
 - 4.4. Suma de Picos
 - 4.5. Algoritmos de Ordenación
    - 4.5.1. Ordenación por Selección (Selection Sort)
    - 4.5.2. Ordenación por Mezclas (Mergesort)
 - 4.6. Recursión sobre Árboles Binarios
- README.md

CONTENIDO:

En cada uno de los apartados se incluyen archivos .dfy con:
  - El código inicial sin especificaciones (funcional pero no verificado).
  - El código inicial con especificaciones generadas automáticamente mediante el uso de ChatGPT y distintos prompts. Los prompts usados para generar las especificaciones aparecen al inicio de cada código para los que han sido requeridos, seguidos de la salida obtenida, es decir, del código especificado ya mencionado. 

El código llamado Extra.BinarySearch_Prompt3.dfy, no aparece en la memoria del TFG, pero se menciona al hacer la comparativa en la Sección 4.3 (Cuadro 4.1).

Además de los archivos en Dafny, se incluyen dos scripts en Python generados automáticamente con ChatGPT:
  - BinarySearch_Prompt2_Python.py: versión iterativa de búsqueda binaria generada a partir del Prompt 2.
  - Sum_AB_Prompt1_Python.py: función de suma de los elementos de un Árbol Binario con especificación generada a partir del Prompt 1.

CÓMO USAR LOS CÓDIGOS:

Para trabajar con los archivos .dfy se ha utilizado Visual Studio Code, junto con la extensión oficial de Dafny (versión recomendada: v3.4.4 o superior (incluye el verificador Z3)).
Una vez instalada la extensión, basta con abrir un archivo .dfy en VS Code y Dafny realizará la verificación automáticamente del código al guardarlo (Ctrl+S).
