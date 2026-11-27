---
theme: book
title: ¿Qué divide a dos enteros consecutivos?
stem: vecinos
---

# ¿Qué divide a dos enteros consecutivos?

Si un número divide a 20 y a 21, también divide a 1. ¿Puedes demostrarlo sin enumerar los divisores de ninguno de los dos? Esta es la pieza que después usaremos en la prueba de Euclides. Para construirla aprenderemos dos operaciones: recuperar un hecho que ya conocemos y elegir un número que haga verdadera una afirmación.

## Un paso que ya sabemos dar

Supón que sabes que llueve y hace frío. Si te preguntan si llueve, basta con recuperar la primera parte de lo que sabes. Cambiemos «llueve» y «hace frío» por dos proposiciones cualesquiera, $P$ y $Q$. El mismo argumento sirve sin averiguar qué significan.

```python {export=vecinos.py}
import logos
from logos import Prop, Int, exists

@logos.theorem
def first_fact(P: Prop, Q: Prop):
    return (P & Q) >> P

@first_fact.proof
def prove_first(p, P, Q):
    both = p.assume(P & Q)
    return both.left()
```

El primer bloque de la definición enuncia una implicación. En el cuerpo de la prueba, `p` representa el estado de ese argumento: qué podemos usar y qué queda por probar. Al escribir `assume` entramos en el antecedente de la implicación. La hipótesis queda limitada a ese argumento. Devolver evidencia de $P$ cierra el consecuente. Si devolviéramos `both.right()`, la interfaz debería poder decir «obtuviste Q; aquí hace falta P». Esa observación basta para seguir trabajando incluso cuando no sabemos nada sobre la lluvia.

## Un número que cumple lo prometido

¿Qué significa «$d$ divide a $a$»? Que hay un número $k$ tal que $a=dk$. Por ejemplo, para demostrar que 3 divide a 21 puedes entregar el 7. Trabajaremos con enteros. Así un cociente también puede ser negativo.

```python {export=vecinos.py}
@logos.definition
def divides(d: Int, a: Int):
    return exists(Int, lambda k: a == d * k)
```

La suma de dos pares es par. Puedes empezar por dos pares pequeños, pero la prueba debe funcionar para cualquiera. Sean $a=2i$ y $b=2j$. ¿Qué número entregarías al pedirte la mitad de $a+b$? La elección $i+j$ es la idea de la prueba.

```python {export=vecinos.py}
@logos.theorem
def even_sum(a: Int, b: Int):
    return (divides(2, a) & divides(2, b)) >> divides(2, a+b)

@even_sum.proof
def prove_sum(p, a, b):
    pairs = p.assume(divides(2, a) & divides(2, b))
    i, ha = p.obtain(pairs.left())
    j, hb = p.obtain(pairs.right())
    total = p.ring(a + b == 2 * (i + j), using=[ha, hb])
    return p.witness(i + j, total)
```

Hay dos movimientos diferentes. Con `obtain` abrimos una afirmación de existencia ya demostrada. Recibimos un nombre local y el hecho preciso que lo acompaña. Con `witness` hacemos el recorrido inverso: elegimos el número y damos la evidencia que se nos pide sobre él. Así podemos cerrar la prueba con un enunciado que ya no menciona ni $i$ ni $j$.

## Dos vecinos

Ensaya ahora una pregunta más difícil: si $d$ divide tanto a $a$ como a $a+1$, ¿qué más tiene que dividir? Toma como ejemplo dos múltiplos de 5. Al restarlos siempre obtienes otro múltiplo de 5. Si fueran consecutivos, su diferencia sería 1.

De $a=dk$ y $a+1=dj$ obtenemos $1=d(j-k)$. Antes de leer el código, fíjate en el orden de la resta. ¿Qué igualdad demostraría $k-j$?

```python {export=vecinos.py}
@logos.theorem
def common_divisor(d: Int, a: Int):
    return (divides(d, a) & divides(d, a+1)) >> divides(d, 1)

@common_divisor.proof
def prove_difference(p, d, a):
    h = p.assume(divides(d, a) & divides(d, a+1))
    k, left = p.obtain(h.left())
    j, right = p.obtain(h.right())
    quotient = j - k
    one = p.ring(1 == d * quotient, using=[left, right])
    return p.witness(quotient, one)
```

Prueba el cambio $k-j$ con $d=1$ y $a=4$. Los testigos son 4 y 5. La igualdad que necesitas se convierte en $1=-1$. Has encontrado un contraejemplo al paso que acabas de escribir. El lema sigue siendo verdadero: acabamos de demostrarlo con la resta en el otro sentido.


## Compruébalo con Logos

```python {export=vecinos.py}
if __name__ == "__main__":
    first_fact.check()
    even_sum.check()
    common_divisor.check()
    logos.export_proof(common_divisor, "vecinos.logos")
```

Desde un directorio con esta página guardada como `vecinos.md`, Scriptorium, el paquete Python de Logos y su verificador Rust instalados, ejecuta:

```bash
scriptorium tangle vecinos.md
python vecinos.py
logos check --strict vecinos.logos
```

Ahora cambia **solo** `quotient = j - k` por `quotient = k - j` en la página. Vuelve a extraer el programa y a ejecutarlo. Cuando llegues a la igualdad que falla, busca las dos hipótesis que nombramos `left` y `right`. ¿Cuál de las dos te da el producto mayor en el ejemplo con 4 y 5? Restaura el signo y repite los tres comandos para generar y verificar el certificado corregido.
