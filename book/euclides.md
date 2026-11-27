---
theme: book
title: Siempre queda otro primo
stem: euclides
---

# Siempre queda otro primo

Imagina que alguien te entrega una tabla de números primos y te asegura que está completa. ¿Cómo le responderías si la tabla fuera tan larga que no pudieras buscar el siguiente primo a mano? Euclides tuvo una idea mejor que continuar la búsqueda: usa la propia tabla para construir un número que obligue a mirar fuera de ella.

Al terminar tendremos un teorema con una entrada y una promesa precisas: para cada entero $n$ mayor o igual que dos, existe un primo $q$ mayor que $n$. Por el camino aprenderemos a usar una hipótesis, a elegir un testigo, a razonar por inducción y a guardar un argumento para usarlo después como lema.

Este capítulo es un programa. Los bloques marcados con `export=euclides.py` se extraen en orden con `scriptorium tangle` y forman un único módulo ejecutable. Las definiciones y las pruebas son las que se leen en la página, no una versión resumida escondida en una biblioteca.

## La divisibilidad que ya conocemos

¿Qué significa «$d$ divide a $a$»? Que hay un entero $k$ tal que $a=dk$. Por ejemplo, para demostrar que 3 divide a 21 puedes entregar el 7. Trabajamos con enteros, así que un cociente también puede ser negativo.

```python {export=euclides.py}

import logos
from logos import Int, exists, forall, lit

@logos.definition
def divides(d: Int, a: Int):
    return exists(Int, lambda k: a == d * k)
```

[La lección anterior](vecinos.md) ya demostró el hecho que necesitamos sobre dos enteros consecutivos. La copiamos con la misma definición transparente y la misma prueba, sin cambiar su contenido matemático. Si $d$ divide a $a$ y también a $a+1$, entonces divide a la diferencia, que es 1. Los testigos son $k$ y $j$; el cociente que buscamos es $j-k$.

```python {export=euclides.py}

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

El primer bloque de una prueba enuncia una implicación. En el cuerpo, `p` representa el estado del argumento: qué podemos usar y qué queda por probar. `assume` entra en el antecedente. `obtain` abre una afirmación de existencia ya demostrada y recibe un nombre local y su igualdad. `ring` comprueba una identidad entera a partir de las igualdades abiertas. `witness` hace el recorrido inverso: elige el entero que cumple la afirmación existencial y entrega la evidencia.

## Tres herramientas de divisibilidad

Antes de atacar primos y factoriales necesitamos tres consecuencias pequeñas. La primera dice que todo entero se divide a sí mismo. El testigo natural es 1.

```python {export=euclides.py}

@logos.theorem
def divides_self(d: Int):
    return divides(d, d)

@divides_self.proof
def prove_divides_self(p, d):
    product = p.ring(d == d * 1)
    return p.witness(1, product)
```

La segunda dice que la divisibilidad es transitiva. Si $a$ divide a $b$ con cociente $k$, y $b$ divide a $c$ con cociente $j$, entonces $c=bj=(ak)j=a(kj)$. El testigo es el producto de los dos cocientes.

```python {export=euclides.py}

@logos.theorem
def divides_trans(a: Int, b: Int, c: Int):
    return (divides(a, b) & divides(b, c)) >> divides(a, c)

@divides_trans.proof
def prove_divides_trans(p, a, b, c):
    h = p.assume(divides(a, b) & divides(b, c))
    k, left = p.obtain(h.left())
    j, right = p.obtain(h.right())
    product = p.ring(c == a * (k * j), using=[left, right])
    return p.witness(k * j, product)
```

La tercera permite multiplicar el dividendo por un entero cualquiera. Si $b=ak$, entonces $cb=c(ak)=a(kc)$. El testigo cambia de $k$ a $kc$.

```python {export=euclides.py}

@logos.theorem
def divides_mul(a: Int, b: Int, c: Int):
    return divides(a, b) >> divides(a, c * b)

@divides_mul.proof
def prove_divides_mul(p, a, b, c):
    h = p.assume(divides(a, b))
    k, product = p.obtain(h)
    scaled = p.ring(c * b == a * (k * c), using=[product])
    return p.witness(k * c, scaled)
```

Cada prueba termina con un testigo y una igualdad. El verificador no confía en el nombre del testigo: comprueba que la igualdad instanciada sea exactamente la que exige la afirmación existencial.

## Un primo no divide a uno

Un primo es mayor que uno y ningún divisor propio lo divide. Para la contradicción final necesitamos un hecho más simple: si $d>1$, entonces $d$ no divide a 1. La prueba usa la ley de los enteros que dice que un producto igual a 1 obliga a que sus factores sean 1 o -1.

```python {export=euclides.py}

@logos.theorem
def not_dvd_one(d: Int):
    return (1 < d) >> ~divides(d, 1)

@not_dvd_one.proof
def prove_not_dvd_one(p, d):
    above = p.assume(1 < d)
    with p.negate() as suppose:
        q, one_eq = p.obtain(suppose.assumption)
        product_one = p.symm(one_eq)
        split = p.order("mul_eq_one", d, q, using=[product_one])
        with p.cases(split) as cases:
            with cases.left() as d_one:
                cases.finish(p.linear(False, using=[above, d_one]))
            with cases.right() as d_minus_one:
                cases.finish(p.linear(False, using=[above, d_minus_one]))
        suppose.finish(cases.result)
    return suppose.result
```

`p.negate()` abre la negación del objetivo: para probar «no $A$», supone $A$ y pide una contradicción. Después `p.cases` separa la disyunción en dos ramas. En la primera, $d=1$ choca con $1<d$. En la segunda, $d=-1$ también choca con $1<d$. La aritmética lineal convierte cada par de hipótesis en una contradicción explícita.

## El factorial y su positividad

El factorial reúne muchos divisores en un solo número. Definimos $0!=1$ y $(k+1)!=(k+1)k!$. La segunda ecuación es la que usa la inducción. En Logos una función recursiva se declara con sus dos ecuaciones y el verificador las comprueba cuando se citan.

```python {export=euclides.py}

factorial = logos.recursor("factorial", 1, lambda n, previous: (n + 1) * previous)
```

Queremos demostrar que $n!$ es positivo cuando $n$ no es negativo. La prueba es una inducción ordinaria. El caso base usa $0!=1$. En el paso, la hipótesis de inducción dice $0<k!$. Como $k$ no es negativo, $0<k+1$. El producto de dos positivos es positivo, y la ecuación del factorial lo traslada a $(k+1)!$.

```python {export=euclides.py}

@logos.theorem
def factorial_positive(n: Int):
    return ~(n < 0) >> (0 < factorial(n))

@factorial_positive.proof
def prove_factorial_positive(p, n):
    nonnegative = p.assume(~(n < 0))
    with p.induction(n, 0, nonnegative=nonnegative) as induction:
        with induction.base() as base:
            zero_eq = p.recursor_base(factorial)
            base.finish(p.linear(0 < factorial(0), using=[zero_eq]))
        with induction.step() as step:
            k = step.variable
            previous = step.hypothesis
            successor = p.order("lt_succ_rev", 0, k, using=[step.nonnegative])
            product_positive = p.order(
                "mul_pos", k + 1, factorial(k),
                using=[successor, previous],
            )
            step_eq = p.recursor_step(factorial, k, step.nonnegative)
            step.finish(p.subst(product_positive, p.symm(step_eq)))
    return induction.result
```

La inducción tiene tres piezas visibles. `induction.base()` es el caso $n=0$. `induction.step()` entrega una variable arbitraria $k$, la hipótesis de que $k$ no es negativo y la hipótesis de inducción para $k$. El resultado es la conclusión para $k+1$. Logos combina las tres y devuelve el teorema para todo $n$ no negativo.

Para la cota inferior del número que vamos a fabricar necesitamos algo más fuerte: si $n\ge 2$, entonces $1<n!$. La prueba vuelve a ser una inducción, esta vez desde 2. Antes de escribirla necesitamos dos identidades auxiliares. La primera reparte un producto por un sucesor; la segunda dice que sumar un entero positivo a un número mayor conserva la desigualdad.

```python {export=euclides.py}

@logos.theorem
def mul_succ(k: Int, f: Int):
    return (k + 1) * f == f + k * f

@mul_succ.proof
def prove_mul_succ(p, k, f):
    return p.ring((k + 1) * f == f + k * f)

@logos.theorem
def lt_add_pos(a: Int, b: Int, c: Int):
    return (a < b) >> ((0 < c) >> (a < b + c))

@lt_add_pos.proof
def prove_lt_add_pos(p, a, b, c):
    below = p.assume(a < b)
    positive = p.assume(0 < c)
    return p.linear(a < b + c, using=[below, positive])
```

La prueba de $1<n!$ para $n\ge2$ usa el caso base $2!=2$. En el paso escribimos $(k+1)!= (k+1)k! = k! + k\cdot k!$. La hipótesis de inducción da $1<k!$, y $k\cdot k!$ es positivo porque $k\ge2$. Entonces la suma es mayor que 1. Las constantes se escriben con `lit` para que Python construya la misma expresión simbólica que aparece en la meta, en lugar de calcularla como un número de Python.

```python {export=euclides.py}

@logos.theorem
def factorial_above_one(n: Int):
    return ~(n < 2) >> (1 < factorial(n))

@factorial_above_one.proof
def prove_factorial_above_one(p, n):
    at_least_two = p.assume(~(n < 2))
    with p.induction(n, 2, nonnegative=at_least_two) as induction:
        with induction.base() as base:
            zero_lt_one = p.linear(lit(0) < lit(1))
            not_one_lt_zero = p.not_lt_of_lt(lit(0), lit(1), zero_lt_one)
            not_zero_lt_zero = p.order("lt_irrefl", 0)
            step0 = p.recursor_step(factorial, 0, not_zero_lt_zero)
            base_eq = p.recursor_base(factorial)
            step1 = p.recursor_step(factorial, 1, not_one_lt_zero)
            one_is = p.ring(lit(0) + lit(1) == lit(1))
            two_is = p.ring(lit(1) + lit(1) == lit(2))
            step0_one = p.subst(step0, one_is)
            step1_two = p.subst(step1, two_is)
            two_eq = p.ring(
                factorial(2) == 2,
                using=[step1_two, step0_one, base_eq],
            )
            base.finish(p.linear(lit(1) < factorial(2), using=[two_eq]))
        with induction.step() as step:
            k = step.variable
            previous = step.hypothesis
            two_le_k = p.order("not_lt_le", k, 2, using=[step.nonnegative])
            zero_lt_k = p.linear(0 < k, using=[two_le_k])
            not_k_below_zero = p.not_lt_of_lt(0, k, zero_lt_k)
            positive_factorial = p.apply(
                factorial_positive, k, not_k_below_zero
            )
            product_positive = p.order(
                "mul_pos", k, factorial(k),
                using=[zero_lt_k, positive_factorial],
            )
            step_eq = p.recursor_step(factorial, k, not_k_below_zero)
            distributed = p.apply(mul_succ, k, factorial(k))
            decomposed = p.trans(step_eq, distributed)
            larger = p.apply(
                lt_add_pos, 1, factorial(k), k * factorial(k),
                previous, product_positive,
            )
            step.finish(p.subst(larger, p.symm(decomposed)))
    return induction.result
```

En el paso, `p.apply(mul_succ, ...)` es una aplicación de lema con nombre. `p.trans` encadena dos igualdades y comprueba que el término del medio coincida. `p.subst` reescribe una desigualdad usando una igualdad. Ninguno de esos pasos es un atajo del teorema: cada uno produce evidencia que el verificador Rust vuelve a comprobar.

## Todo divisor hasta n divide a n!

Ahora queremos demostrar que si $1<d$ y $d<n+1$, entonces $d$ divide a $n!$. La inducción ordinaria vuelve a bastar. En el caso base $n=0$ no hay ningún $d$ con $1<d<1$. En el paso hay dos posibilidades para $d$: o ya estaba por debajo de $k+1$, o es exactamente $k+1$.

En la primera posibilidad usamos la hipótesis de inducción para obtener $d\mid k!$ y multiplicamos el dividendo por $k+1$. La ecuación del factorial convierte $(k+1)k!$ en $(k+1)!$. En la segunda, la cota superior y la decisión de que no es menor que $k+1$ obligan a $d=k+1$; el testigo de la divisibilidad es entonces $k!$.

```python {export=euclides.py}

@logos.theorem
def factorial_dvd(n: Int):
    return ~(n < 0) >> forall(Int, lambda d:
        (1 < d) >> ((d < n + 1) >> divides(d, factorial(n))))

@factorial_dvd.proof
def prove_factorial_dvd(p, n):
    nonnegative = p.assume(~(n < 0))
    with p.induction(n, 0, nonnegative=nonnegative) as induction:
        with induction.base() as base:
            with p.fix("d") as fixed:
                d = fixed.variable
                above = p.assume(1 < d)
                below = p.assume(d < lit(0) + lit(1))
                clash = p.linear(False, using=[above, below])
                fixed.finish(p.ex_falso(clash))
            base.finish(fixed.result)
        with induction.step() as step:
            k = step.variable
            with p.fix("d") as fixed:
                d = fixed.variable
                above = p.assume(1 < d)
                bound = p.assume(d < (k + 1) + 1)
                decision = p.order("lt_decidable", d, k + 1)
                with p.cases(decision) as cases:
                    with cases.left() as smaller:
                        ih = p.apply(step.hypothesis, d, above, smaller)
                        multiplied = p.apply(
                            divides_mul, d, factorial(k), k + 1, ih
                        )
                        step_eq = p.recursor_step(
                            factorial, k, step.nonnegative
                        )
                        cases.finish(p.subst(multiplied, p.symm(step_eq)))
                    with cases.right() as not_smaller:
                        forward = p.order(
                            "lt_succ_fwd", d, k + 1, using=[bound]
                        )
                        equal = p.order(
                            "eq_of_not_lt_not_lt", d, k + 1,
                            using=[not_smaller, forward],
                        )
                        step_eq = p.recursor_step(
                            factorial, k, step.nonnegative
                        )
                        same = p.refl(d * factorial(k))
                        moved = p.subst(same, equal)
                        equation = p.trans(step_eq, moved)
                        cases.finish(p.witness(factorial(k), equation))
                fixed.finish(cases.result)
            step.finish(fixed.result)
    return induction.result
```

`p.fix("d")` introduce el $d$ arbitrario del `forall` interior. La decisión `p.order("lt_decidable", d, k + 1)` es una disyunción comprobada: el verificador conoce la ley y no acepta una rama inventada. En la rama derecha, `p.refl` crea la igualdad trivial $d\cdot k! = d\cdot k!$ y `p.subst` la reescribe con $d=k+1$. Así el testigo $k!$ queda conectado con la ecuación del factorial.

## El divisor más pequeño

Llamaremos primo a un entero $q$ mayor que uno cuyos únicos divisores positivos son 1 y $q$. La definición que usamos dice que no existe un divisor $d$ estrictamente entre 1 y $q$.

```python {export=euclides.py}

@logos.definition
def prime(q: Int):
    return (1 < q) & ~exists(Int, lambda d:
        (1 < d) & ((d < q) & divides(d, q)))
```

Queremos probar que todo entero $m>1$ tiene un divisor primo $q$, y que ese $q$ divide a $m$. La idea es elegir el divisor más pequeño de $m$ que sea mayor que 1. Ese divisor no puede ser compuesto: si tuviera un divisor propio $d$, entonces $d$ también dividiría a $m$ y sería un divisor más pequeño, en contradicción con la elección.

Para usar el principio del mínimo necesitamos primero un conjunto no vacío. El propio $m$ es un divisor de $m$ y es mayor que 1, así que sirve como testigo. La regla del mínimo devuelve el menor $q$ junto con dos datos: $q$ pertenece al conjunto y ningún entero menor, todavía mayor que 1, pertenece.

```python {export=euclides.py}

@logos.theorem
def least_prime_divisor(m: Int):
    return (1 < m) >> exists(Int, lambda q: prime(q) & divides(q, m))

@least_prime_divisor.proof
def prove_least_prime_divisor(p, m):
    above_one = p.assume(1 < m)
    self_divisor = p.apply(divides_self, m)
    below_one = p.not_lt_of_lt(1, m, above_one)
    member = p.and_intro(below_one, p.and_intro(above_one, self_divisor))
    nonempty = p.exists(
        exists(Int, lambda d: ~(d < 1) & ((1 < d) & divides(d, m))),
        m,
        member,
    )
    least = p.least(1, nonempty)
    q, properties = p.obtain(least)
    bounds = properties.left()
    q_properties = bounds.right()
    q_above_one = q_properties.left()
    q_dvd_m = q_properties.right()
    minimal = properties.right()
    proper_exists = exists(Int, lambda d:
        (1 < d) & ((d < q) & divides(d, q)))
    with p.negate(~proper_exists) as suppose:
        d, proper = p.obtain(suppose.assumption)
        d_above_one = proper.left()
        d_below_q = proper.right().left()
        d_dvd_q = proper.right().right()
        d_dvd_m = p.apply(
            divides_trans, d, q, m,
            p.and_intro(d_dvd_q, q_dvd_m),
        )
        not_below_one = p.not_lt_of_lt(1, d, d_above_one)
        smaller = p.and_intro(not_below_one, d_below_q)
        no_proper = p.apply(minimal, d, smaller)
        clash = p.not_elim(no_proper, p.and_intro(d_above_one, d_dvd_m))
        suppose.finish(clash)
    q_prime = p.and_intro(q_above_one, suppose.result)
    return p.witness(q, p.and_intro(q_prime, q_dvd_m))
```

La prueba de que $q$ es primo tiene la forma de una contradicción. Suponemos que existe un divisor propio $d$. La minimalidad de $q$ dice que ningún $d$ menor, con $1<d$, divide a $m$. Pero la transitividad de la divisibilidad muestra que $d$ divide a $m$, y tenemos $1<d$ y $d<q$. Esa es la contradicción. El testigo final es $q$, con la primalidad y la divisibilidad del original $m$.

## Siempre queda otro primo

Ya podemos atacar la tabla de primos. Para $n=5$, el producto de todos los naturales hasta 5 es 120; al sumarle uno obtenemos 121. Este ejemplo tiene una ventaja sobre uno en el que salga un primo por casualidad.

```{python}
from math import factorial
m = factorial(5) + 1
print(m, "=", 11, "×", m // 11)
assert m == 11 * 11 and 11 > 5
```

El número construido puede ser compuesto. Nos basta con uno de sus divisores primos. Llamémoslo $q$. Si $q$ fuera como máximo $n$, dividiría a $n!$ por la divisibilidad del factorial. Por construcción también divide a $n!+1$. El lema de los dos vecinos dice que entonces dividiría a 1. Pero un primo es mayor que uno, y ya demostramos que ningún entero mayor que uno divide a 1.

```python {export=euclides.py}

@logos.theorem
def euclid(n: Int):
    return ~(n < 2) >> exists(Int, lambda q: prime(q) & (n < q))

@euclid.proof
def prove_euclid(p, n):
    at_least_two = p.assume(~(n < 2))
    f = factorial(n)
    above_f = p.apply(factorial_above_one, n, at_least_two)
    m = f + 1
    above_m = p.linear(1 < m, using=[above_f])
    q, factor = p.obtain(p.apply(least_prime_divisor, m, above_m))
    q_prime = factor.left()
    q_dvd_m = factor.right()
    q_above_one = q_prime.left()
    with p.contradict(n < q) as contrary:
        not_n_lt_q = contrary.hypothesis
        q_lt_succ = p.order("lt_succ_rev", q, n, using=[not_n_lt_q])
        two_le_n = p.order("not_lt_le", n, 2, using=[at_least_two])
        zero_lt_n = p.linear(0 < n, using=[two_le_n])
        not_n_below_zero = p.not_lt_of_lt(0, n, zero_lt_n)
        q_dvd_f = p.apply(
            factorial_dvd, n, not_n_below_zero, q, q_above_one, q_lt_succ
        )
        neighbors = p.and_intro(q_dvd_f, q_dvd_m)
        divides_one = p.apply(common_divisor, q, f, neighbors)
        no_one = p.apply(not_dvd_one, q, q_above_one)
        contrary.finish(p.not_elim(no_one, divides_one))
    return p.witness(q, p.and_intro(q_prime, contrary.result))
```

El paso `above_m = p.linear(1 < m, using=[above_f])` merece atención. La prueba ya sabe que $1<f$. La aritmética lineal deduce $1<f+1$. Si en la página se cambiara el número fabricado de $f+1$ a $f$, esa misma línea seguiría siendo válida, porque $1<f$ es exactamente lo que ya teníamos. El error aparecería más adelante, en el lugar donde se usa el lema de los vecinos.

La hipótesis $2\le n$ se usa para obtener $0<n$, y de ahí la positividad del factorial y la cota $q<n+1$. La contradicción supone $n\ge q$; la ley del sucesor la convierte en $q<n+1$. Entonces $q$ divide a $n!$ y a $n!+1$. El lema `common_divisor(q, f)` recibe esas dos divisibilidades y devuelve $q\mid1$. La prueba de `not_dvd_one(q)` choca con eso. El testigo final es el primo $q$, y la conclusión `contrary.result` es $n<q$.

## Compruébalo con Logos

El módulo extraído comprueba cada lema y exporta el certificado del teorema final. El archivo `.logos` no necesita Python para verificarse: lo lee el ejecutable Rust.

```python {export=euclides.py}
if __name__ == "__main__":
    divides_self.check()
    divides_trans.check()
    divides_mul.check()
    common_divisor.check()
    not_dvd_one.check()
    factorial_positive.check()
    factorial_above_one.check()
    factorial_dvd.check()
    least_prime_divisor.check()
    euclid.check()
    logos.export_proof(euclid, "euclides.logos")
```

Desde un directorio con esta página guardada como `euclides.md`, Scriptorium, el paquete Python de Logos y su verificador Rust instalados, ejecuta:

```bash
scriptorium tangle euclides.md
python euclides.py
logos check --strict euclides.logos
```

La última orden debe responder `Verified with 0 custom axioms`. El certificado incluye los lemas usados y sus pruebas, no solo la conclusión final. La teoría `logos-core-v1` aporta la inducción, la recursión del factorial, el principio del mínimo y las leyes de orden; el capítulo no declara ningún axioma propio.

## El control negativo

Ahora cambia **solo** la línea `m = f + 1` por `m = f` en la página. Vuelve a extraer el programa y ejecútalo. La prueba llega hasta la aplicación de `common_divisor`, porque la cota `1 < m` sigue siendo verdadera. Allí falla: el lema espera dos divisibilidades, $q\mid f$ y $q\mid(f+1)$, pero recibe $q\mid f$ dos veces.

El error muestra la línea culpable, la meta que se estaba probando, el antecedente esperado y la evidencia recibida. En los datos estructurados aparecen además el lema `common_divisor`, el número de argumento y las líneas relacionadas. No se escribe ningún certificado nuevo. Restaura el signo, repite los tres comandos y el certificado vuelve a verificarse con cero axiomas propios.

## Qué debe poder comprobar el lector

La fuente de Scriptorium reúne los fragmentos en orden con `scriptorium tangle euclides.md`. El archivo extraído conserva las mismas decisiones matemáticas que se ven en estas páginas: la definición transparente de divisibilidad, la prueba de los dos vecinos, el mínimo divisor, la positividad y la divisibilidad del factorial, y la contradicción final.

La prueba de aceptación ejecuta ese archivo desde el wheel instalado, exporta el teorema y lo verifica en un proceso independiente con el ejecutable Rust. También cambia la línea del número fabricado y exige que el fallo ocurra en la aplicación del lema de los vecinos, no antes. Si el lector puede señalar en la página la hipótesis de inducción, el testigo de cada rama, la minimalidad del divisor y la contradicción final, entonces el capítulo cumplió su propósito.
